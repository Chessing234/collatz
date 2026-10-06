import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0949

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 31064. -/
theorem bounds_15_31064 : exactInterval 15 31064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31064 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31064) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31064 : oddCount 31064 15 = 6 ∧ acceleratedOrbit 15 31064 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31064 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31064) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31064.1, data_15_31064.2]

/-- Complete interval computation for depth 15, residue 31065. -/
theorem bounds_15_31065 : exactInterval 15 31065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31065 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31065) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31065 : oddCount 31065 15 = 7 ∧ acceleratedOrbit 15 31065 = 2074 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31065 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31065) = 3 ^ 7 * m + 2074 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31065.1, data_15_31065.2]

/-- Complete interval computation for depth 15, residue 31066. -/
theorem bounds_15_31066 : exactInterval 15 31066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31066 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31066) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31066 : oddCount 31066 15 = 6 ∧ acceleratedOrbit 15 31066 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31066 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31066) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31066.1, data_15_31066.2]

/-- Complete interval computation for depth 15, residue 31067. -/
theorem bounds_15_31067 : exactInterval 15 31067 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31067 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31067) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31067 : oddCount 31067 15 = 8 ∧ acceleratedOrbit 15 31067 = 6221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31067 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31067) = 3 ^ 8 * m + 6221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31067.1, data_15_31067.2]

/-- Complete interval computation for depth 15, residue 31068. -/
theorem bounds_15_31068 : exactInterval 15 31068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31068 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31068) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31068 : oddCount 31068 15 = 6 ∧ acceleratedOrbit 15 31068 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31068 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31068) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31068.1, data_15_31068.2]

/-- Complete interval computation for depth 15, residue 31069. -/
theorem bounds_15_31069 : exactInterval 15 31069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31069 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31069) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31069 : oddCount 31069 15 = 6 ∧ acceleratedOrbit 15 31069 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31069 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31069) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31069.1, data_15_31069.2]

/-- Complete interval computation for depth 15, residue 31070. -/
theorem bounds_15_31070 : exactInterval 15 31070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31070 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31070) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31070 : oddCount 31070 15 = 10 ∧ acceleratedOrbit 15 31070 = 55997 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31070 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31070) = 3 ^ 10 * m + 55997 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31070.1, data_15_31070.2]

/-- Complete interval computation for depth 15, residue 31071. -/
theorem bounds_15_31071 : exactInterval 15 31071 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31071 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31071) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31071 : oddCount 31071 15 = 10 ∧ acceleratedOrbit 15 31071 = 55997 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31071 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31071) = 3 ^ 10 * m + 55997 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31071.1, data_15_31071.2]

/-- Complete interval computation for depth 15, residue 31072. -/
theorem bounds_15_31072 : exactInterval 15 31072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31072 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31072) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31072 : oddCount 31072 15 = 4 ∧ acceleratedOrbit 15 31072 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31072 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31072) = 3 ^ 4 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31072.1, data_15_31072.2]

/-- Complete interval computation for depth 15, residue 31073. -/
theorem bounds_15_31073 : exactInterval 15 31073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31073 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31073) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31073 : oddCount 31073 15 = 9 ∧ acceleratedOrbit 15 31073 = 18667 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31073 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31073) = 3 ^ 9 * m + 18667 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31073.1, data_15_31073.2]

/-- Complete interval computation for depth 15, residue 31074. -/
theorem bounds_15_31074 : exactInterval 15 31074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31074 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31074) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31074 : oddCount 31074 15 = 8 ∧ acceleratedOrbit 15 31074 = 6227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31074 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31074) = 3 ^ 8 * m + 6227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31074.1, data_15_31074.2]

/-- Complete interval computation for depth 15, residue 31075. -/
theorem bounds_15_31075 : exactInterval 15 31075 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31075 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31075) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31075 : oddCount 31075 15 = 8 ∧ acceleratedOrbit 15 31075 = 6227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31075 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31075) = 3 ^ 8 * m + 6227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31075.1, data_15_31075.2]

/-- Complete interval computation for depth 15, residue 31076. -/
theorem bounds_15_31076 : exactInterval 15 31076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31076 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31076) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31076 : oddCount 31076 15 = 8 ∧ acceleratedOrbit 15 31076 = 6227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31076 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31076) = 3 ^ 8 * m + 6227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31076.1, data_15_31076.2]

/-- Complete interval computation for depth 15, residue 31077. -/
theorem bounds_15_31077 : exactInterval 15 31077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31077 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31077) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31077 : oddCount 31077 15 = 8 ∧ acceleratedOrbit 15 31077 = 6227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31077 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31077) = 3 ^ 8 * m + 6227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31077.1, data_15_31077.2]

/-- Complete interval computation for depth 15, residue 31078. -/
theorem bounds_15_31078 : exactInterval 15 31078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31078 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31078) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31078 : oddCount 31078 15 = 8 ∧ acceleratedOrbit 15 31078 = 6227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31078 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31078) = 3 ^ 8 * m + 6227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31078.1, data_15_31078.2]

/-- Complete interval computation for depth 15, residue 31079. -/
theorem bounds_15_31079 : exactInterval 15 31079 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31079 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31079) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31079 : oddCount 31079 15 = 10 ∧ acceleratedOrbit 15 31079 = 56008 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31079 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31079) = 3 ^ 10 * m + 56008 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31079.1, data_15_31079.2]

/-- Complete interval computation for depth 15, residue 31080. -/
theorem bounds_15_31080 : exactInterval 15 31080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31080 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31080) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31080 : oddCount 31080 15 = 4 ∧ acceleratedOrbit 15 31080 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31080 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31080) = 3 ^ 4 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31080.1, data_15_31080.2]

/-- Complete interval computation for depth 15, residue 31081. -/
theorem bounds_15_31081 : exactInterval 15 31081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31081 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31081) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31081 : oddCount 31081 15 = 6 ∧ acceleratedOrbit 15 31081 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31081 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31081) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31081.1, data_15_31081.2]

/-- Complete interval computation for depth 15, residue 31082. -/
theorem bounds_15_31082 : exactInterval 15 31082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31082 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31082) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31082 : oddCount 31082 15 = 4 ∧ acceleratedOrbit 15 31082 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31082 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31082) = 3 ^ 4 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31082.1, data_15_31082.2]

/-- Complete interval computation for depth 15, residue 31083. -/
theorem bounds_15_31083 : exactInterval 15 31083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31083 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31083) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31083 : oddCount 31083 15 = 9 ∧ acceleratedOrbit 15 31083 = 18674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31083 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31083) = 3 ^ 9 * m + 18674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31083.1, data_15_31083.2]

/-- Complete interval computation for depth 15, residue 31084. -/
theorem bounds_15_31084 : exactInterval 15 31084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31084 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31084) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31084 : oddCount 31084 15 = 7 ∧ acceleratedOrbit 15 31084 = 2075 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31084 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31084) = 3 ^ 7 * m + 2075 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31084.1, data_15_31084.2]

/-- Complete interval computation for depth 15, residue 31085. -/
theorem bounds_15_31085 : exactInterval 15 31085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31085 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31085) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31085 : oddCount 31085 15 = 7 ∧ acceleratedOrbit 15 31085 = 2075 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31085 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31085) = 3 ^ 7 * m + 2075 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31085.1, data_15_31085.2]

/-- Complete interval computation for depth 15, residue 31086. -/
theorem bounds_15_31086 : exactInterval 15 31086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31086 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31086) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31086 : oddCount 31086 15 = 7 ∧ acceleratedOrbit 15 31086 = 2075 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31086 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31086) = 3 ^ 7 * m + 2075 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31086.1, data_15_31086.2]

/-- Complete interval computation for depth 15, residue 31087. -/
theorem bounds_15_31087 : exactInterval 15 31087 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31087 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31087) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31087 : oddCount 31087 15 = 7 ∧ acceleratedOrbit 15 31087 = 2075 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31087 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31087) = 3 ^ 7 * m + 2075 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31087.1, data_15_31087.2]

/-- Complete interval computation for depth 15, residue 31088. -/
theorem bounds_15_31088 : exactInterval 15 31088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31088 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31088) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31088 : oddCount 31088 15 = 4 ∧ acceleratedOrbit 15 31088 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31088 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31088) = 3 ^ 4 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31088.1, data_15_31088.2]

/-- Complete interval computation for depth 15, residue 31089. -/
theorem bounds_15_31089 : exactInterval 15 31089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31089 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31089) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31089 : oddCount 31089 15 = 4 ∧ acceleratedOrbit 15 31089 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31089 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31089) = 3 ^ 4 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31089.1, data_15_31089.2]

/-- Complete interval computation for depth 15, residue 31090. -/
theorem bounds_15_31090 : exactInterval 15 31090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31090 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31090) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31090 : oddCount 31090 15 = 8 ∧ acceleratedOrbit 15 31090 = 6227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31090 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31090) = 3 ^ 8 * m + 6227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31090.1, data_15_31090.2]

/-- Complete interval computation for depth 15, residue 31091. -/
theorem bounds_15_31091 : exactInterval 15 31091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31091 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31091) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31091 : oddCount 31091 15 = 8 ∧ acceleratedOrbit 15 31091 = 6227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31091 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31091) = 3 ^ 8 * m + 6227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31091.1, data_15_31091.2]

/-- Complete interval computation for depth 15, residue 31092. -/
theorem bounds_15_31092 : exactInterval 15 31092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31092 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31092) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31092 : oddCount 31092 15 = 4 ∧ acceleratedOrbit 15 31092 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31092 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31092) = 3 ^ 4 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31092.1, data_15_31092.2]

/-- Complete interval computation for depth 15, residue 31093. -/
theorem bounds_15_31093 : exactInterval 15 31093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31093 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31093) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31093 : oddCount 31093 15 = 4 ∧ acceleratedOrbit 15 31093 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31093 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31093) = 3 ^ 4 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31093.1, data_15_31093.2]

/-- Complete interval computation for depth 15, residue 31094. -/
theorem bounds_15_31094 : exactInterval 15 31094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31094 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31094) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31094 : oddCount 31094 15 = 10 ∧ acceleratedOrbit 15 31094 = 56042 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31094 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31094) = 3 ^ 10 * m + 56042 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31094.1, data_15_31094.2]

/-- Complete interval computation for depth 15, residue 31095. -/
theorem bounds_15_31095 : exactInterval 15 31095 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31095 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31095) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31095 : oddCount 31095 15 = 10 ∧ acceleratedOrbit 15 31095 = 56042 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31095 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31095) = 3 ^ 10 * m + 56042 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31095.1, data_15_31095.2]

end Collatz.Research.PassageAtlas.Batch0949
