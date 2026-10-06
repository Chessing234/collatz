import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0644

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 21069. -/
theorem bounds_15_21069 : exactInterval 15 21069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21069 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21069) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21069 : oddCount 21069 15 = 6 ∧ acceleratedOrbit 15 21069 = 469 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21069 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21069) = 3 ^ 6 * m + 469 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21069.1, data_15_21069.2]

/-- Complete interval computation for depth 15, residue 21070. -/
theorem bounds_15_21070 : exactInterval 15 21070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21070 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21070) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21070 : oddCount 21070 15 = 8 ∧ acceleratedOrbit 15 21070 = 4220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21070 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21070) = 3 ^ 8 * m + 4220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21070.1, data_15_21070.2]

/-- Complete interval computation for depth 15, residue 21071. -/
theorem bounds_15_21071 : exactInterval 15 21071 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21071 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21071) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21071 : oddCount 21071 15 = 8 ∧ acceleratedOrbit 15 21071 = 4220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21071 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21071) = 3 ^ 8 * m + 4220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21071.1, data_15_21071.2]

/-- Complete interval computation for depth 15, residue 21072. -/
theorem bounds_15_21072 : exactInterval 15 21072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21072 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21072) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21072 : oddCount 21072 15 = 5 ∧ acceleratedOrbit 15 21072 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21072 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21072) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21072.1, data_15_21072.2]

/-- Complete interval computation for depth 15, residue 21073. -/
theorem bounds_15_21073 : exactInterval 15 21073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21073 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21073) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21073 : oddCount 21073 15 = 9 ∧ acceleratedOrbit 15 21073 = 12662 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21073 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21073) = 3 ^ 9 * m + 12662 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21073.1, data_15_21073.2]

/-- Complete interval computation for depth 15, residue 21074. -/
theorem bounds_15_21074 : exactInterval 15 21074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21074 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21074) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21074 : oddCount 21074 15 = 9 ∧ acceleratedOrbit 15 21074 = 12662 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21074 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21074) = 3 ^ 9 * m + 12662 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21074.1, data_15_21074.2]

/-- Complete interval computation for depth 15, residue 21075. -/
theorem bounds_15_21075 : exactInterval 15 21075 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21075 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21075) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21075 : oddCount 21075 15 = 9 ∧ acceleratedOrbit 15 21075 = 12662 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21075 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21075) = 3 ^ 9 * m + 12662 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21075.1, data_15_21075.2]

/-- Complete interval computation for depth 15, residue 21076. -/
theorem bounds_15_21076 : exactInterval 15 21076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21076 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21076) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21076 : oddCount 21076 15 = 5 ∧ acceleratedOrbit 15 21076 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21076 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21076) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21076.1, data_15_21076.2]

/-- Complete interval computation for depth 15, residue 21077. -/
theorem bounds_15_21077 : exactInterval 15 21077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21077 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21077) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21077 : oddCount 21077 15 = 5 ∧ acceleratedOrbit 15 21077 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21077 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21077) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21077.1, data_15_21077.2]

/-- Complete interval computation for depth 15, residue 21078. -/
theorem bounds_15_21078 : exactInterval 15 21078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21078 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21078) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21078 : oddCount 21078 15 = 8 ∧ acceleratedOrbit 15 21078 = 4222 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21078 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21078) = 3 ^ 8 * m + 4222 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21078.1, data_15_21078.2]

/-- Complete interval computation for depth 15, residue 21079. -/
theorem bounds_15_21079 : exactInterval 15 21079 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21079 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21079) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21079 : oddCount 21079 15 = 8 ∧ acceleratedOrbit 15 21079 = 4222 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21079 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21079) = 3 ^ 8 * m + 4222 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21079.1, data_15_21079.2]

/-- Complete interval computation for depth 15, residue 21080. -/
theorem bounds_15_21080 : exactInterval 15 21080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21080 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21080) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21080 : oddCount 21080 15 = 5 ∧ acceleratedOrbit 15 21080 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21080 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21080) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21080.1, data_15_21080.2]

/-- Complete interval computation for depth 15, residue 21081. -/
theorem bounds_15_21081 : exactInterval 15 21081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21081 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21081) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21081 : oddCount 21081 15 = 8 ∧ acceleratedOrbit 15 21081 = 4222 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21081 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21081) = 3 ^ 8 * m + 4222 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21081.1, data_15_21081.2]

/-- Complete interval computation for depth 15, residue 21082. -/
theorem bounds_15_21082 : exactInterval 15 21082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21082 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21082) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21082 : oddCount 21082 15 = 5 ∧ acceleratedOrbit 15 21082 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21082 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21082) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21082.1, data_15_21082.2]

/-- Complete interval computation for depth 15, residue 21083. -/
theorem bounds_15_21083 : exactInterval 15 21083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21083 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21083) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21083 : oddCount 21083 15 = 11 ∧ acceleratedOrbit 15 21083 = 113987 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21083 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21083) = 3 ^ 11 * m + 113987 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21083.1, data_15_21083.2]

/-- Complete interval computation for depth 15, residue 21084. -/
theorem bounds_15_21084 : exactInterval 15 21084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21084 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21084) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21084 : oddCount 21084 15 = 5 ∧ acceleratedOrbit 15 21084 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21084 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21084) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21084.1, data_15_21084.2]

/-- Complete interval computation for depth 15, residue 21085. -/
theorem bounds_15_21085 : exactInterval 15 21085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21085 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21085) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21085 : oddCount 21085 15 = 5 ∧ acceleratedOrbit 15 21085 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21085 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21085) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21085.1, data_15_21085.2]

/-- Complete interval computation for depth 15, residue 21086. -/
theorem bounds_15_21086 : exactInterval 15 21086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21086 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21086) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21086 : oddCount 21086 15 = 8 ∧ acceleratedOrbit 15 21086 = 4223 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21086 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21086) = 3 ^ 8 * m + 4223 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21086.1, data_15_21086.2]

/-- Complete interval computation for depth 15, residue 21087. -/
theorem bounds_15_21087 : exactInterval 15 21087 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21087 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21087) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21087 : oddCount 21087 15 = 8 ∧ acceleratedOrbit 15 21087 = 4223 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21087 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21087) = 3 ^ 8 * m + 4223 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21087.1, data_15_21087.2]

/-- Complete interval computation for depth 15, residue 21088. -/
theorem bounds_15_21088 : exactInterval 15 21088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21088 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21088) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21088 : oddCount 21088 15 = 5 ∧ acceleratedOrbit 15 21088 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21088 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21088) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21088.1, data_15_21088.2]

/-- Complete interval computation for depth 15, residue 21089. -/
theorem bounds_15_21089 : exactInterval 15 21089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21089 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21089) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21089 : oddCount 21089 15 = 7 ∧ acceleratedOrbit 15 21089 = 1408 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21089 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21089) = 3 ^ 7 * m + 1408 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21089.1, data_15_21089.2]

/-- Complete interval computation for depth 15, residue 21090. -/
theorem bounds_15_21090 : exactInterval 15 21090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21090 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21090) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21090 : oddCount 21090 15 = 6 ∧ acceleratedOrbit 15 21090 = 470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21090 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21090) = 3 ^ 6 * m + 470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21090.1, data_15_21090.2]

/-- Complete interval computation for depth 15, residue 21091. -/
theorem bounds_15_21091 : exactInterval 15 21091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21091 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21091) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21091 : oddCount 21091 15 = 6 ∧ acceleratedOrbit 15 21091 = 470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21091 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21091) = 3 ^ 6 * m + 470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21091.1, data_15_21091.2]

/-- Complete interval computation for depth 15, residue 21092. -/
theorem bounds_15_21092 : exactInterval 15 21092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21092 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21092) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21092 : oddCount 21092 15 = 6 ∧ acceleratedOrbit 15 21092 = 470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21092 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21092) = 3 ^ 6 * m + 470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21092.1, data_15_21092.2]

/-- Complete interval computation for depth 15, residue 21093. -/
theorem bounds_15_21093 : exactInterval 15 21093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21093 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21093) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21093 : oddCount 21093 15 = 6 ∧ acceleratedOrbit 15 21093 = 470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21093 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21093) = 3 ^ 6 * m + 470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21093.1, data_15_21093.2]

/-- Complete interval computation for depth 15, residue 21094. -/
theorem bounds_15_21094 : exactInterval 15 21094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21094 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21094) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21094 : oddCount 21094 15 = 6 ∧ acceleratedOrbit 15 21094 = 470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21094 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21094) = 3 ^ 6 * m + 470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21094.1, data_15_21094.2]

/-- Complete interval computation for depth 15, residue 21095. -/
theorem bounds_15_21095 : exactInterval 15 21095 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21095 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21095) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21095 : oddCount 21095 15 = 7 ∧ acceleratedOrbit 15 21095 = 1408 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21095 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21095) = 3 ^ 7 * m + 1408 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21095.1, data_15_21095.2]

/-- Complete interval computation for depth 15, residue 21096. -/
theorem bounds_15_21096 : exactInterval 15 21096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21096 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21096) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21096 : oddCount 21096 15 = 5 ∧ acceleratedOrbit 15 21096 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21096 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21096) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21096.1, data_15_21096.2]

/-- Complete interval computation for depth 15, residue 21097. -/
theorem bounds_15_21097 : exactInterval 15 21097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21097 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21097) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21097 : oddCount 21097 15 = 9 ∧ acceleratedOrbit 15 21097 = 12674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21097 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21097) = 3 ^ 9 * m + 12674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21097.1, data_15_21097.2]

/-- Complete interval computation for depth 15, residue 21098. -/
theorem bounds_15_21098 : exactInterval 15 21098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21098 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21098) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21098 : oddCount 21098 15 = 5 ∧ acceleratedOrbit 15 21098 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21098 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21098) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21098.1, data_15_21098.2]

/-- Complete interval computation for depth 15, residue 21099. -/
theorem bounds_15_21099 : exactInterval 15 21099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21099 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21099) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21099 : oddCount 21099 15 = 9 ∧ acceleratedOrbit 15 21099 = 12676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21099 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21099) = 3 ^ 9 * m + 12676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21099.1, data_15_21099.2]

/-- Complete interval computation for depth 15, residue 21100. -/
theorem bounds_15_21100 : exactInterval 15 21100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21100 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21100) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21100 : oddCount 21100 15 = 8 ∧ acceleratedOrbit 15 21100 = 4226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21100 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21100) = 3 ^ 8 * m + 4226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21100.1, data_15_21100.2]

/-- Complete interval computation for depth 15, residue 21101. -/
theorem bounds_15_21101 : exactInterval 15 21101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21101 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21101) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21101 : oddCount 21101 15 = 8 ∧ acceleratedOrbit 15 21101 = 4226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21101 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21101) = 3 ^ 8 * m + 4226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21101.1, data_15_21101.2]

end Collatz.Research.PassageAtlas.Batch0644
