import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0603

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2078. -/
theorem bounds_13_2078 : exactInterval 13 2078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2078 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2078) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2078 : oddCount 2078 13 = 7 ∧ acceleratedOrbit 13 2078 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2078 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2078) = 3 ^ 7 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2078.1, data_13_2078.2]

/-- Complete interval computation for depth 13, residue 2079. -/
theorem bounds_13_2079 : exactInterval 13 2079 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2079 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2079) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2079 : oddCount 2079 13 = 8 ∧ acceleratedOrbit 13 2079 = 1666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2079 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2079) = 3 ^ 8 * m + 1666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2079.1, data_13_2079.2]

/-- Complete interval computation for depth 13, residue 2080. -/
theorem bounds_13_2080 : exactInterval 13 2080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2080 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2080) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2080 : oddCount 2080 13 = 3 ∧ acceleratedOrbit 13 2080 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2080 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2080) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2080.1, data_13_2080.2]

/-- Complete interval computation for depth 13, residue 2081. -/
theorem bounds_13_2081 : exactInterval 13 2081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2081 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2081) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2081 : oddCount 2081 13 = 7 ∧ acceleratedOrbit 13 2081 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2081 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2081) = 3 ^ 7 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2081.1, data_13_2081.2]

/-- Complete interval computation for depth 13, residue 2082. -/
theorem bounds_13_2082 : exactInterval 13 2082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2082 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2082) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2082 : oddCount 2082 13 = 6 ∧ acceleratedOrbit 13 2082 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2082 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2082) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2082.1, data_13_2082.2]

/-- Complete interval computation for depth 13, residue 2083. -/
theorem bounds_13_2083 : exactInterval 13 2083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2083 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2083) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2083 : oddCount 2083 13 = 6 ∧ acceleratedOrbit 13 2083 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2083 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2083) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2083.1, data_13_2083.2]

/-- Complete interval computation for depth 13, residue 2084. -/
theorem bounds_13_2084 : exactInterval 13 2084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2084 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2084) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2084 : oddCount 2084 13 = 5 ∧ acceleratedOrbit 13 2084 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2084 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2084) = 3 ^ 5 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2084.1, data_13_2084.2]

/-- Complete interval computation for depth 13, residue 2085. -/
theorem bounds_13_2085 : exactInterval 13 2085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2085 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2085) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2085 : oddCount 2085 13 = 5 ∧ acceleratedOrbit 13 2085 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2085 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2085) = 3 ^ 5 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2085.1, data_13_2085.2]

/-- Complete interval computation for depth 13, residue 2086. -/
theorem bounds_13_2086 : exactInterval 13 2086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2086 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2086) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2086 : oddCount 2086 13 = 5 ∧ acceleratedOrbit 13 2086 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2086 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2086) = 3 ^ 5 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2086.1, data_13_2086.2]

/-- Complete interval computation for depth 13, residue 2087. -/
theorem bounds_13_2087 : exactInterval 13 2087 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2087 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2087) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2087 : oddCount 2087 13 = 9 ∧ acceleratedOrbit 13 2087 = 5021 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2087 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2087) = 3 ^ 9 * m + 5021 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2087.1, data_13_2087.2]

/-- Complete interval computation for depth 13, residue 2088. -/
theorem bounds_13_2088 : exactInterval 13 2088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2088 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2088) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2088 : oddCount 2088 13 = 3 ∧ acceleratedOrbit 13 2088 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2088 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2088) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2088.1, data_13_2088.2]

/-- Complete interval computation for depth 13, residue 2089. -/
theorem bounds_13_2089 : exactInterval 13 2089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2089 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2089) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2089 : oddCount 2089 13 = 9 ∧ acceleratedOrbit 13 2089 = 5024 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2089 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2089) = 3 ^ 9 * m + 5024 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2089.1, data_13_2089.2]

/-- Complete interval computation for depth 13, residue 2090. -/
theorem bounds_13_2090 : exactInterval 13 2090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2090 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2090) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2090 : oddCount 2090 13 = 3 ∧ acceleratedOrbit 13 2090 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2090 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2090) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2090.1, data_13_2090.2]

/-- Complete interval computation for depth 13, residue 2091. -/
theorem bounds_13_2091 : exactInterval 13 2091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2091 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2091) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2091 : oddCount 2091 13 = 7 ∧ acceleratedOrbit 13 2091 = 560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2091 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2091) = 3 ^ 7 * m + 560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2091.1, data_13_2091.2]

/-- Complete interval computation for depth 13, residue 2092. -/
theorem bounds_13_2092 : exactInterval 13 2092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2092 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2092) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2092 : oddCount 2092 13 = 6 ∧ acceleratedOrbit 13 2092 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2092 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2092) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2092.1, data_13_2092.2]

/-- Complete interval computation for depth 13, residue 2093. -/
theorem bounds_13_2093 : exactInterval 13 2093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2093 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2093) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2093 : oddCount 2093 13 = 6 ∧ acceleratedOrbit 13 2093 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2093 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2093) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2093.1, data_13_2093.2]

end Collatz.Research.StoppingAtlas.Batch0603
