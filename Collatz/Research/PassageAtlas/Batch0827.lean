import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0827

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 27066. -/
theorem bounds_15_27066 : exactInterval 15 27066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27066 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27066) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27066 : oddCount 27066 15 = 8 ∧ acceleratedOrbit 15 27066 = 5422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27066 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27066) = 3 ^ 8 * m + 5422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27066.1, data_15_27066.2]

/-- Complete interval computation for depth 15, residue 27067. -/
theorem bounds_15_27067 : exactInterval 15 27067 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27067 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27067) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27067 : oddCount 27067 15 = 10 ∧ acceleratedOrbit 15 27067 = 48782 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27067 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27067) = 3 ^ 10 * m + 48782 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27067.1, data_15_27067.2]

/-- Complete interval computation for depth 15, residue 27068. -/
theorem bounds_15_27068 : exactInterval 15 27068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27068 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27068) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27068 : oddCount 27068 15 = 10 ∧ acceleratedOrbit 15 27068 = 48788 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27068 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27068) = 3 ^ 10 * m + 48788 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27068.1, data_15_27068.2]

/-- Complete interval computation for depth 15, residue 27069. -/
theorem bounds_15_27069 : exactInterval 15 27069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27069 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27069) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27069 : oddCount 27069 15 = 10 ∧ acceleratedOrbit 15 27069 = 48788 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27069 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27069) = 3 ^ 10 * m + 48788 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27069.1, data_15_27069.2]

/-- Complete interval computation for depth 15, residue 27070. -/
theorem bounds_15_27070 : exactInterval 15 27070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27070 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27070) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27070 : oddCount 27070 15 = 10 ∧ acceleratedOrbit 15 27070 = 48788 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27070 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27070) = 3 ^ 10 * m + 48788 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27070.1, data_15_27070.2]

/-- Complete interval computation for depth 15, residue 27071. -/
theorem bounds_15_27071 : exactInterval 15 27071 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27071 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27071) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27071 : oddCount 27071 15 = 12 ∧ acceleratedOrbit 15 27071 = 439064 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27071 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27071) = 3 ^ 12 * m + 439064 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27071.1, data_15_27071.2]

/-- Complete interval computation for depth 15, residue 27072. -/
theorem bounds_15_27072 : exactInterval 15 27072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27072 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27072) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27072 : oddCount 27072 15 = 6 ∧ acceleratedOrbit 15 27072 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27072 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27072) = 3 ^ 6 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27072.1, data_15_27072.2]

/-- Complete interval computation for depth 15, residue 27073. -/
theorem bounds_15_27073 : exactInterval 15 27073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27073 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27073) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27073 : oddCount 27073 15 = 8 ∧ acceleratedOrbit 15 27073 = 5422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27073 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27073) = 3 ^ 8 * m + 5422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27073.1, data_15_27073.2]

/-- Complete interval computation for depth 15, residue 27074. -/
theorem bounds_15_27074 : exactInterval 15 27074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27074 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27074) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27074 : oddCount 27074 15 = 11 ∧ acceleratedOrbit 15 27074 = 146393 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27074 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27074) = 3 ^ 11 * m + 146393 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27074.1, data_15_27074.2]

/-- Complete interval computation for depth 15, residue 27075. -/
theorem bounds_15_27075 : exactInterval 15 27075 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27075 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27075) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27075 : oddCount 27075 15 = 11 ∧ acceleratedOrbit 15 27075 = 146393 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27075 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27075) = 3 ^ 11 * m + 146393 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27075.1, data_15_27075.2]

/-- Complete interval computation for depth 15, residue 27076. -/
theorem bounds_15_27076 : exactInterval 15 27076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27076 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27076) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27076 : oddCount 27076 15 = 5 ∧ acceleratedOrbit 15 27076 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27076 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27076) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27076.1, data_15_27076.2]

/-- Complete interval computation for depth 15, residue 27077. -/
theorem bounds_15_27077 : exactInterval 15 27077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27077 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27077) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27077 : oddCount 27077 15 = 5 ∧ acceleratedOrbit 15 27077 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27077 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27077) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27077.1, data_15_27077.2]

/-- Complete interval computation for depth 15, residue 27078. -/
theorem bounds_15_27078 : exactInterval 15 27078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27078 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27078) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27078 : oddCount 27078 15 = 5 ∧ acceleratedOrbit 15 27078 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27078 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27078) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27078.1, data_15_27078.2]

/-- Complete interval computation for depth 15, residue 27079. -/
theorem bounds_15_27079 : exactInterval 15 27079 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27079 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27079) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27079 : oddCount 27079 15 = 10 ∧ acceleratedOrbit 15 27079 = 48802 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27079 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27079) = 3 ^ 10 * m + 48802 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27079.1, data_15_27079.2]

/-- Complete interval computation for depth 15, residue 27080. -/
theorem bounds_15_27080 : exactInterval 15 27080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27080 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27080) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27080 : oddCount 27080 15 = 9 ∧ acceleratedOrbit 15 27080 = 16280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27080 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27080) = 3 ^ 9 * m + 16280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27080.1, data_15_27080.2]

/-- Complete interval computation for depth 15, residue 27081. -/
theorem bounds_15_27081 : exactInterval 15 27081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27081 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27081) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27081 : oddCount 27081 15 = 9 ∧ acceleratedOrbit 15 27081 = 16271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27081 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27081) = 3 ^ 9 * m + 16271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27081.1, data_15_27081.2]

/-- Complete interval computation for depth 15, residue 27082. -/
theorem bounds_15_27082 : exactInterval 15 27082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27082 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27082) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27082 : oddCount 27082 15 = 9 ∧ acceleratedOrbit 15 27082 = 16280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27082 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27082) = 3 ^ 9 * m + 16280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27082.1, data_15_27082.2]

/-- Complete interval computation for depth 15, residue 27083. -/
theorem bounds_15_27083 : exactInterval 15 27083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27083 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27083) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27083 : oddCount 27083 15 = 8 ∧ acceleratedOrbit 15 27083 = 5426 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27083 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27083) = 3 ^ 8 * m + 5426 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27083.1, data_15_27083.2]

/-- Complete interval computation for depth 15, residue 27084. -/
theorem bounds_15_27084 : exactInterval 15 27084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27084 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27084) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27084 : oddCount 27084 15 = 9 ∧ acceleratedOrbit 15 27084 = 16280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27084 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27084) = 3 ^ 9 * m + 16280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27084.1, data_15_27084.2]

/-- Complete interval computation for depth 15, residue 27085. -/
theorem bounds_15_27085 : exactInterval 15 27085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27085 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27085) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27085 : oddCount 27085 15 = 9 ∧ acceleratedOrbit 15 27085 = 16280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27085 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27085) = 3 ^ 9 * m + 16280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27085.1, data_15_27085.2]

/-- Complete interval computation for depth 15, residue 27086. -/
theorem bounds_15_27086 : exactInterval 15 27086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27086 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27086) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27086 : oddCount 27086 15 = 11 ∧ acceleratedOrbit 15 27086 = 146447 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27086 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27086) = 3 ^ 11 * m + 146447 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27086.1, data_15_27086.2]

/-- Complete interval computation for depth 15, residue 27087. -/
theorem bounds_15_27087 : exactInterval 15 27087 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27087 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27087) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27087 : oddCount 27087 15 = 11 ∧ acceleratedOrbit 15 27087 = 146447 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27087 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27087) = 3 ^ 11 * m + 146447 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27087.1, data_15_27087.2]

/-- Complete interval computation for depth 15, residue 27088. -/
theorem bounds_15_27088 : exactInterval 15 27088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27088 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27088) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27088 : oddCount 27088 15 = 6 ∧ acceleratedOrbit 15 27088 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27088 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27088) = 3 ^ 6 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27088.1, data_15_27088.2]

/-- Complete interval computation for depth 15, residue 27089. -/
theorem bounds_15_27089 : exactInterval 15 27089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27089 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27089) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27089 : oddCount 27089 15 = 9 ∧ acceleratedOrbit 15 27089 = 16280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27089 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27089) = 3 ^ 9 * m + 16280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27089.1, data_15_27089.2]

/-- Complete interval computation for depth 15, residue 27090. -/
theorem bounds_15_27090 : exactInterval 15 27090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27090 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27090) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27090 : oddCount 27090 15 = 8 ∧ acceleratedOrbit 15 27090 = 5426 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27090 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27090) = 3 ^ 8 * m + 5426 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27090.1, data_15_27090.2]

/-- Complete interval computation for depth 15, residue 27091. -/
theorem bounds_15_27091 : exactInterval 15 27091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27091 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27091) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27091 : oddCount 27091 15 = 8 ∧ acceleratedOrbit 15 27091 = 5426 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27091 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27091) = 3 ^ 8 * m + 5426 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27091.1, data_15_27091.2]

/-- Complete interval computation for depth 15, residue 27092. -/
theorem bounds_15_27092 : exactInterval 15 27092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27092 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27092) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27092 : oddCount 27092 15 = 6 ∧ acceleratedOrbit 15 27092 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27092 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27092) = 3 ^ 6 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27092.1, data_15_27092.2]

/-- Complete interval computation for depth 15, residue 27093. -/
theorem bounds_15_27093 : exactInterval 15 27093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27093 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27093) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27093 : oddCount 27093 15 = 6 ∧ acceleratedOrbit 15 27093 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27093 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27093) = 3 ^ 6 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27093.1, data_15_27093.2]

/-- Complete interval computation for depth 15, residue 27094. -/
theorem bounds_15_27094 : exactInterval 15 27094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27094 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27094) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27094 : oddCount 27094 15 = 10 ∧ acceleratedOrbit 15 27094 = 48833 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27094 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27094) = 3 ^ 10 * m + 48833 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27094.1, data_15_27094.2]

/-- Complete interval computation for depth 15, residue 27095. -/
theorem bounds_15_27095 : exactInterval 15 27095 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27095 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27095) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27095 : oddCount 27095 15 = 10 ∧ acceleratedOrbit 15 27095 = 48833 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27095 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27095) = 3 ^ 10 * m + 48833 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27095.1, data_15_27095.2]

/-- Complete interval computation for depth 15, residue 27096. -/
theorem bounds_15_27096 : exactInterval 15 27096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27096 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27096) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27096 : oddCount 27096 15 = 4 ∧ acceleratedOrbit 15 27096 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27096 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27096) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27096.1, data_15_27096.2]

/-- Complete interval computation for depth 15, residue 27097. -/
theorem bounds_15_27097 : exactInterval 15 27097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27097 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27097) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27097 : oddCount 27097 15 = 4 ∧ acceleratedOrbit 15 27097 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27097 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27097) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27097.1, data_15_27097.2]

/-- Complete interval computation for depth 15, residue 27098. -/
theorem bounds_15_27098 : exactInterval 15 27098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27098 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27098) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27098 : oddCount 27098 15 = 4 ∧ acceleratedOrbit 15 27098 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27098 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27098) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27098.1, data_15_27098.2]

end Collatz.Research.PassageAtlas.Batch0827
