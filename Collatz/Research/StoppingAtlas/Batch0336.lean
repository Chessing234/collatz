import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0336

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2073. -/
theorem bounds_12_2073 : exactInterval 12 2073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2073 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2073) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2073 : oddCount 2073 12 = 7 ∧ acceleratedOrbit 12 2073 = 1109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2073 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2073) = 3 ^ 7 * m + 1109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2073.1, data_12_2073.2]

/-- Complete interval computation for depth 12, residue 2074. -/
theorem bounds_12_2074 : exactInterval 12 2074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2074 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2074) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2074 : oddCount 2074 12 = 5 ∧ acceleratedOrbit 12 2074 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2074 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2074) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2074.1, data_12_2074.2]

/-- Complete interval computation for depth 12, residue 2075. -/
theorem bounds_12_2075 : exactInterval 12 2075 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2075 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2075) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2075 : oddCount 2075 12 = 8 ∧ acceleratedOrbit 12 2075 = 3326 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2075 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2075) = 3 ^ 8 * m + 3326 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2075.1, data_12_2075.2]

/-- Complete interval computation for depth 12, residue 2076. -/
theorem bounds_12_2076 : exactInterval 12 2076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2076 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2076) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2076 : oddCount 2076 12 = 6 ∧ acceleratedOrbit 12 2076 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2076 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2076) = 3 ^ 6 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2076.1, data_12_2076.2]

/-- Complete interval computation for depth 12, residue 2077. -/
theorem bounds_12_2077 : exactInterval 12 2077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2077 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2077) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2077 : oddCount 2077 12 = 6 ∧ acceleratedOrbit 12 2077 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2077 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2077) = 3 ^ 6 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2077.1, data_12_2077.2]

/-- Complete interval computation for depth 12, residue 2078. -/
theorem bounds_12_2078 : exactInterval 12 2078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2078 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2078) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2078 : oddCount 2078 12 = 6 ∧ acceleratedOrbit 12 2078 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2078 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2078) = 3 ^ 6 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2078.1, data_12_2078.2]

/-- Complete interval computation for depth 12, residue 2079. -/
theorem bounds_12_2079 : exactInterval 12 2079 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2079 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2079) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2079 : oddCount 2079 12 = 8 ∧ acceleratedOrbit 12 2079 = 3332 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2079 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2079) = 3 ^ 8 * m + 3332 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2079.1, data_12_2079.2]

/-- Complete interval computation for depth 12, residue 2080. -/
theorem bounds_12_2080 : exactInterval 12 2080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2080 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2080) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2080 : oddCount 2080 12 = 3 ∧ acceleratedOrbit 12 2080 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2080 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2080) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2080.1, data_12_2080.2]

/-- Complete interval computation for depth 12, residue 2081. -/
theorem bounds_12_2081 : exactInterval 12 2081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2081 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2081) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2081 : oddCount 2081 12 = 6 ∧ acceleratedOrbit 12 2081 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2081 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2081) = 3 ^ 6 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2081.1, data_12_2081.2]

/-- Complete interval computation for depth 12, residue 2082. -/
theorem bounds_12_2082 : exactInterval 12 2082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2082 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2082) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2082 : oddCount 2082 12 = 5 ∧ acceleratedOrbit 12 2082 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2082 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2082) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2082.1, data_12_2082.2]

/-- Complete interval computation for depth 12, residue 2083. -/
theorem bounds_12_2083 : exactInterval 12 2083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2083 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2083) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2083 : oddCount 2083 12 = 5 ∧ acceleratedOrbit 12 2083 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2083 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2083) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2083.1, data_12_2083.2]

/-- Complete interval computation for depth 12, residue 2084. -/
theorem bounds_12_2084 : exactInterval 12 2084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2084 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2084) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2084 : oddCount 2084 12 = 5 ∧ acceleratedOrbit 12 2084 = 124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2084 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2084) = 3 ^ 5 * m + 124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2084.1, data_12_2084.2]

/-- Complete interval computation for depth 12, residue 2085. -/
theorem bounds_12_2085 : exactInterval 12 2085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2085 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2085) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2085 : oddCount 2085 12 = 5 ∧ acceleratedOrbit 12 2085 = 124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2085 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2085) = 3 ^ 5 * m + 124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2085.1, data_12_2085.2]

/-- Complete interval computation for depth 12, residue 2086. -/
theorem bounds_12_2086 : exactInterval 12 2086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2086 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2086) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2086 : oddCount 2086 12 = 5 ∧ acceleratedOrbit 12 2086 = 124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2086 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2086) = 3 ^ 5 * m + 124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2086.1, data_12_2086.2]

/-- Complete interval computation for depth 12, residue 2087. -/
theorem bounds_12_2087 : exactInterval 12 2087 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2087 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2087) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2087 : oddCount 2087 12 = 8 ∧ acceleratedOrbit 12 2087 = 3347 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2087 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2087) = 3 ^ 8 * m + 3347 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2087.1, data_12_2087.2]

end Collatz.Research.StoppingAtlas.Batch0336
