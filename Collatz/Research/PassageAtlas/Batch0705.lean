import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0705

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 23068. -/
theorem bounds_15_23068 : exactInterval 15 23068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23068 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23068) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23068 : oddCount 23068 15 = 7 ∧ acceleratedOrbit 15 23068 = 1541 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23068 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23068) = 3 ^ 7 * m + 1541 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23068.1, data_15_23068.2]

/-- Complete interval computation for depth 15, residue 23069. -/
theorem bounds_15_23069 : exactInterval 15 23069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23069 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23069) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23069 : oddCount 23069 15 = 7 ∧ acceleratedOrbit 15 23069 = 1541 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23069 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23069) = 3 ^ 7 * m + 1541 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23069.1, data_15_23069.2]

/-- Complete interval computation for depth 15, residue 23070. -/
theorem bounds_15_23070 : exactInterval 15 23070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23070 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23070) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23070 : oddCount 23070 15 = 7 ∧ acceleratedOrbit 15 23070 = 1541 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23070 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23070) = 3 ^ 7 * m + 1541 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23070.1, data_15_23070.2]

/-- Complete interval computation for depth 15, residue 23071. -/
theorem bounds_15_23071 : exactInterval 15 23071 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23071 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23071) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23071 : oddCount 23071 15 = 10 ∧ acceleratedOrbit 15 23071 = 41579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23071 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23071) = 3 ^ 10 * m + 41579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23071.1, data_15_23071.2]

/-- Complete interval computation for depth 15, residue 23072. -/
theorem bounds_15_23072 : exactInterval 15 23072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23072 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23072) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23072 : oddCount 23072 15 = 5 ∧ acceleratedOrbit 15 23072 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23072 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23072) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23072.1, data_15_23072.2]

/-- Complete interval computation for depth 15, residue 23073. -/
theorem bounds_15_23073 : exactInterval 15 23073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23073 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23073) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23073 : oddCount 23073 15 = 7 ∧ acceleratedOrbit 15 23073 = 1541 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23073 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23073) = 3 ^ 7 * m + 1541 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23073.1, data_15_23073.2]

/-- Complete interval computation for depth 15, residue 23074. -/
theorem bounds_15_23074 : exactInterval 15 23074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23074 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23074) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23074 : oddCount 23074 15 = 6 ∧ acceleratedOrbit 15 23074 = 514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23074 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23074) = 3 ^ 6 * m + 514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23074.1, data_15_23074.2]

/-- Complete interval computation for depth 15, residue 23075. -/
theorem bounds_15_23075 : exactInterval 15 23075 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23075 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23075) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23075 : oddCount 23075 15 = 6 ∧ acceleratedOrbit 15 23075 = 514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23075 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23075) = 3 ^ 6 * m + 514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23075.1, data_15_23075.2]

/-- Complete interval computation for depth 15, residue 23076. -/
theorem bounds_15_23076 : exactInterval 15 23076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23076 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23076) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23076 : oddCount 23076 15 = 8 ∧ acceleratedOrbit 15 23076 = 4622 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23076 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23076) = 3 ^ 8 * m + 4622 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23076.1, data_15_23076.2]

/-- Complete interval computation for depth 15, residue 23077. -/
theorem bounds_15_23077 : exactInterval 15 23077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23077 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23077) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23077 : oddCount 23077 15 = 8 ∧ acceleratedOrbit 15 23077 = 4622 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23077 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23077) = 3 ^ 8 * m + 4622 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23077.1, data_15_23077.2]

/-- Complete interval computation for depth 15, residue 23078. -/
theorem bounds_15_23078 : exactInterval 15 23078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23078 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23078) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23078 : oddCount 23078 15 = 8 ∧ acceleratedOrbit 15 23078 = 4622 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23078 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23078) = 3 ^ 8 * m + 4622 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23078.1, data_15_23078.2]

/-- Complete interval computation for depth 15, residue 23079. -/
theorem bounds_15_23079 : exactInterval 15 23079 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23079 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23079) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23079 : oddCount 23079 15 = 7 ∧ acceleratedOrbit 15 23079 = 1541 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23079 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23079) = 3 ^ 7 * m + 1541 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23079.1, data_15_23079.2]

/-- Complete interval computation for depth 15, residue 23080. -/
theorem bounds_15_23080 : exactInterval 15 23080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23080 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23080) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23080 : oddCount 23080 15 = 5 ∧ acceleratedOrbit 15 23080 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23080 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23080) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23080.1, data_15_23080.2]

/-- Complete interval computation for depth 15, residue 23081. -/
theorem bounds_15_23081 : exactInterval 15 23081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23081 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23081) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23081 : oddCount 23081 15 = 10 ∧ acceleratedOrbit 15 23081 = 41597 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23081 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23081) = 3 ^ 10 * m + 41597 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23081.1, data_15_23081.2]

/-- Complete interval computation for depth 15, residue 23082. -/
theorem bounds_15_23082 : exactInterval 15 23082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23082 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23082) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23082 : oddCount 23082 15 = 5 ∧ acceleratedOrbit 15 23082 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23082 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23082) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23082.1, data_15_23082.2]

/-- Complete interval computation for depth 15, residue 23083. -/
theorem bounds_15_23083 : exactInterval 15 23083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23083 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23083) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23083 : oddCount 23083 15 = 6 ∧ acceleratedOrbit 15 23083 = 514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23083 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23083) = 3 ^ 6 * m + 514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23083.1, data_15_23083.2]

/-- Complete interval computation for depth 15, residue 23084. -/
theorem bounds_15_23084 : exactInterval 15 23084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23084 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23084) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23084 : oddCount 23084 15 = 6 ∧ acceleratedOrbit 15 23084 = 514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23084 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23084) = 3 ^ 6 * m + 514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23084.1, data_15_23084.2]

/-- Complete interval computation for depth 15, residue 23085. -/
theorem bounds_15_23085 : exactInterval 15 23085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23085 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23085) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23085 : oddCount 23085 15 = 6 ∧ acceleratedOrbit 15 23085 = 514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23085 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23085) = 3 ^ 6 * m + 514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23085.1, data_15_23085.2]

/-- Complete interval computation for depth 15, residue 23086. -/
theorem bounds_15_23086 : exactInterval 15 23086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23086 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23086) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23086 : oddCount 23086 15 = 6 ∧ acceleratedOrbit 15 23086 = 514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23086 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23086) = 3 ^ 6 * m + 514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23086.1, data_15_23086.2]

/-- Complete interval computation for depth 15, residue 23087. -/
theorem bounds_15_23087 : exactInterval 15 23087 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23087 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23087) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23087 : oddCount 23087 15 = 11 ∧ acceleratedOrbit 15 23087 = 124820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23087 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23087) = 3 ^ 11 * m + 124820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23087.1, data_15_23087.2]

/-- Complete interval computation for depth 15, residue 23088. -/
theorem bounds_15_23088 : exactInterval 15 23088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23088 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23088) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23088 : oddCount 23088 15 = 5 ∧ acceleratedOrbit 15 23088 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23088 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23088) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23088.1, data_15_23088.2]

/-- Complete interval computation for depth 15, residue 23089. -/
theorem bounds_15_23089 : exactInterval 15 23089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23089 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23089) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23089 : oddCount 23089 15 = 8 ∧ acceleratedOrbit 15 23089 = 4625 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23089 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23089) = 3 ^ 8 * m + 4625 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23089.1, data_15_23089.2]

/-- Complete interval computation for depth 15, residue 23090. -/
theorem bounds_15_23090 : exactInterval 15 23090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23090 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23090) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23090 : oddCount 23090 15 = 8 ∧ acceleratedOrbit 15 23090 = 4625 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23090 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23090) = 3 ^ 8 * m + 4625 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23090.1, data_15_23090.2]

/-- Complete interval computation for depth 15, residue 23091. -/
theorem bounds_15_23091 : exactInterval 15 23091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23091 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23091) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23091 : oddCount 23091 15 = 8 ∧ acceleratedOrbit 15 23091 = 4625 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23091 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23091) = 3 ^ 8 * m + 4625 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23091.1, data_15_23091.2]

/-- Complete interval computation for depth 15, residue 23092. -/
theorem bounds_15_23092 : exactInterval 15 23092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23092 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23092) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23092 : oddCount 23092 15 = 5 ∧ acceleratedOrbit 15 23092 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23092 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23092) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23092.1, data_15_23092.2]

/-- Complete interval computation for depth 15, residue 23093. -/
theorem bounds_15_23093 : exactInterval 15 23093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23093 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23093) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23093 : oddCount 23093 15 = 5 ∧ acceleratedOrbit 15 23093 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23093 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23093) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23093.1, data_15_23093.2]

/-- Complete interval computation for depth 15, residue 23094. -/
theorem bounds_15_23094 : exactInterval 15 23094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23094 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23094) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23094 : oddCount 23094 15 = 11 ∧ acceleratedOrbit 15 23094 = 124865 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23094 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23094) = 3 ^ 11 * m + 124865 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23094.1, data_15_23094.2]

/-- Complete interval computation for depth 15, residue 23095. -/
theorem bounds_15_23095 : exactInterval 15 23095 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23095 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23095) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23095 : oddCount 23095 15 = 11 ∧ acceleratedOrbit 15 23095 = 124865 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23095 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23095) = 3 ^ 11 * m + 124865 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23095.1, data_15_23095.2]

/-- Complete interval computation for depth 15, residue 23096. -/
theorem bounds_15_23096 : exactInterval 15 23096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23096 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23096) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23096 : oddCount 23096 15 = 8 ∧ acceleratedOrbit 15 23096 = 4627 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23096 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23096) = 3 ^ 8 * m + 4627 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23096.1, data_15_23096.2]

/-- Complete interval computation for depth 15, residue 23097. -/
theorem bounds_15_23097 : exactInterval 15 23097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23097 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23097) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23097 : oddCount 23097 15 = 9 ∧ acceleratedOrbit 15 23097 = 13877 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23097 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23097) = 3 ^ 9 * m + 13877 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23097.1, data_15_23097.2]

/-- Complete interval computation for depth 15, residue 23098. -/
theorem bounds_15_23098 : exactInterval 15 23098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23098 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23098) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23098 : oddCount 23098 15 = 8 ∧ acceleratedOrbit 15 23098 = 4627 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23098 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23098) = 3 ^ 8 * m + 4627 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23098.1, data_15_23098.2]

/-- Complete interval computation for depth 15, residue 23099. -/
theorem bounds_15_23099 : exactInterval 15 23099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23099 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23099) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23099 : oddCount 23099 15 = 6 ∧ acceleratedOrbit 15 23099 = 514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23099 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23099) = 3 ^ 6 * m + 514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23099.1, data_15_23099.2]

/-- Complete interval computation for depth 15, residue 23100. -/
theorem bounds_15_23100 : exactInterval 15 23100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23100 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23100) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23100 : oddCount 23100 15 = 8 ∧ acceleratedOrbit 15 23100 = 4627 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23100 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23100) = 3 ^ 8 * m + 4627 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23100.1, data_15_23100.2]

end Collatz.Research.PassageAtlas.Batch0705
