import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0064

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 2064. -/
theorem bounds_15_2064 : exactInterval 15 2064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2064 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2064) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2064 : oddCount 2064 15 = 6 ∧ acceleratedOrbit 15 2064 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2064 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2064) = 3 ^ 6 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2064.1, data_15_2064.2]

/-- Complete interval computation for depth 15, residue 2065. -/
theorem bounds_15_2065 : exactInterval 15 2065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2065 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2065) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2065 : oddCount 2065 15 = 6 ∧ acceleratedOrbit 15 2065 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2065 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2065) = 3 ^ 6 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2065.1, data_15_2065.2]

/-- Complete interval computation for depth 15, residue 2066. -/
theorem bounds_15_2066 : exactInterval 15 2066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2066 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2066) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2066 : oddCount 2066 15 = 8 ∧ acceleratedOrbit 15 2066 = 415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2066 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2066) = 3 ^ 8 * m + 415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2066.1, data_15_2066.2]

/-- Complete interval computation for depth 15, residue 2067. -/
theorem bounds_15_2067 : exactInterval 15 2067 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2067 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2067) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2067 : oddCount 2067 15 = 8 ∧ acceleratedOrbit 15 2067 = 415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2067 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2067) = 3 ^ 8 * m + 415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2067.1, data_15_2067.2]

/-- Complete interval computation for depth 15, residue 2068. -/
theorem bounds_15_2068 : exactInterval 15 2068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2068 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2068) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2068 : oddCount 2068 15 = 6 ∧ acceleratedOrbit 15 2068 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2068 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2068) = 3 ^ 6 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2068.1, data_15_2068.2]

/-- Complete interval computation for depth 15, residue 2069. -/
theorem bounds_15_2069 : exactInterval 15 2069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2069 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2069) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2069 : oddCount 2069 15 = 6 ∧ acceleratedOrbit 15 2069 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2069 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2069) = 3 ^ 6 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2069.1, data_15_2069.2]

/-- Complete interval computation for depth 15, residue 2070. -/
theorem bounds_15_2070 : exactInterval 15 2070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2070 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2070) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2070 : oddCount 2070 15 = 6 ∧ acceleratedOrbit 15 2070 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2070 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2070) = 3 ^ 6 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2070.1, data_15_2070.2]

/-- Complete interval computation for depth 15, residue 2071. -/
theorem bounds_15_2071 : exactInterval 15 2071 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2071 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2071) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2071 : oddCount 2071 15 = 6 ∧ acceleratedOrbit 15 2071 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2071 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2071) = 3 ^ 6 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2071.1, data_15_2071.2]

/-- Complete interval computation for depth 15, residue 2072. -/
theorem bounds_15_2072 : exactInterval 15 2072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2072 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2072) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2072 : oddCount 2072 15 = 6 ∧ acceleratedOrbit 15 2072 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2072 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2072) = 3 ^ 6 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2072.1, data_15_2072.2]

/-- Complete interval computation for depth 15, residue 2073. -/
theorem bounds_15_2073 : exactInterval 15 2073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2073 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2073) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2073 : oddCount 2073 15 = 8 ∧ acceleratedOrbit 15 2073 = 416 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2073 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2073) = 3 ^ 8 * m + 416 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2073.1, data_15_2073.2]

/-- Complete interval computation for depth 15, residue 2074. -/
theorem bounds_15_2074 : exactInterval 15 2074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2074 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2074) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2074 : oddCount 2074 15 = 6 ∧ acceleratedOrbit 15 2074 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2074 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2074) = 3 ^ 6 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2074.1, data_15_2074.2]

/-- Complete interval computation for depth 15, residue 2075. -/
theorem bounds_15_2075 : exactInterval 15 2075 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2075 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2075) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2075 : oddCount 2075 15 = 10 ∧ acceleratedOrbit 15 2075 = 3743 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2075 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2075) = 3 ^ 10 * m + 3743 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2075.1, data_15_2075.2]

/-- Complete interval computation for depth 15, residue 2076. -/
theorem bounds_15_2076 : exactInterval 15 2076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2076 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2076) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2076 : oddCount 2076 15 = 8 ∧ acceleratedOrbit 15 2076 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2076 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2076) = 3 ^ 8 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2076.1, data_15_2076.2]

/-- Complete interval computation for depth 15, residue 2077. -/
theorem bounds_15_2077 : exactInterval 15 2077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2077 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2077) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2077 : oddCount 2077 15 = 8 ∧ acceleratedOrbit 15 2077 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2077 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2077) = 3 ^ 8 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2077.1, data_15_2077.2]

/-- Complete interval computation for depth 15, residue 2078. -/
theorem bounds_15_2078 : exactInterval 15 2078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2078 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2078) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2078 : oddCount 2078 15 = 8 ∧ acceleratedOrbit 15 2078 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2078 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2078) = 3 ^ 8 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2078.1, data_15_2078.2]

/-- Complete interval computation for depth 15, residue 2079. -/
theorem bounds_15_2079 : exactInterval 15 2079 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2079 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2079) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2079 : oddCount 2079 15 = 9 ∧ acceleratedOrbit 15 2079 = 1250 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2079 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2079) = 3 ^ 9 * m + 1250 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2079.1, data_15_2079.2]

/-- Complete interval computation for depth 15, residue 2080. -/
theorem bounds_15_2080 : exactInterval 15 2080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2080 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2080) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2080 : oddCount 2080 15 = 5 ∧ acceleratedOrbit 15 2080 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2080 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2080) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2080.1, data_15_2080.2]

/-- Complete interval computation for depth 15, residue 2081. -/
theorem bounds_15_2081 : exactInterval 15 2081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2081 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2081) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2081 : oddCount 2081 15 = 8 ∧ acceleratedOrbit 15 2081 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2081 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2081) = 3 ^ 8 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2081.1, data_15_2081.2]

/-- Complete interval computation for depth 15, residue 2082. -/
theorem bounds_15_2082 : exactInterval 15 2082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2082 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2082) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2082 : oddCount 2082 15 = 6 ∧ acceleratedOrbit 15 2082 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2082 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2082) = 3 ^ 6 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2082.1, data_15_2082.2]

/-- Complete interval computation for depth 15, residue 2083. -/
theorem bounds_15_2083 : exactInterval 15 2083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2083 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2083) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2083 : oddCount 2083 15 = 6 ∧ acceleratedOrbit 15 2083 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2083 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2083) = 3 ^ 6 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2083.1, data_15_2083.2]

/-- Complete interval computation for depth 15, residue 2084. -/
theorem bounds_15_2084 : exactInterval 15 2084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2084 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2084) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2084 : oddCount 2084 15 = 6 ∧ acceleratedOrbit 15 2084 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2084 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2084) = 3 ^ 6 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2084.1, data_15_2084.2]

/-- Complete interval computation for depth 15, residue 2085. -/
theorem bounds_15_2085 : exactInterval 15 2085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2085 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2085) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2085 : oddCount 2085 15 = 6 ∧ acceleratedOrbit 15 2085 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2085 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2085) = 3 ^ 6 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2085.1, data_15_2085.2]

/-- Complete interval computation for depth 15, residue 2086. -/
theorem bounds_15_2086 : exactInterval 15 2086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2086 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2086) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2086 : oddCount 2086 15 = 6 ∧ acceleratedOrbit 15 2086 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2086 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2086) = 3 ^ 6 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2086.1, data_15_2086.2]

/-- Complete interval computation for depth 15, residue 2087. -/
theorem bounds_15_2087 : exactInterval 15 2087 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2087 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2087) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2087 : oddCount 2087 15 = 10 ∧ acceleratedOrbit 15 2087 = 3766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2087 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2087) = 3 ^ 10 * m + 3766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2087.1, data_15_2087.2]

/-- Complete interval computation for depth 15, residue 2088. -/
theorem bounds_15_2088 : exactInterval 15 2088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2088 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2088) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2088 : oddCount 2088 15 = 5 ∧ acceleratedOrbit 15 2088 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2088 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2088) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2088.1, data_15_2088.2]

/-- Complete interval computation for depth 15, residue 2089. -/
theorem bounds_15_2089 : exactInterval 15 2089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2089 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2089) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2089 : oddCount 2089 15 = 9 ∧ acceleratedOrbit 15 2089 = 1256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2089 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2089) = 3 ^ 9 * m + 1256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2089.1, data_15_2089.2]

/-- Complete interval computation for depth 15, residue 2090. -/
theorem bounds_15_2090 : exactInterval 15 2090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2090 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2090) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2090 : oddCount 2090 15 = 5 ∧ acceleratedOrbit 15 2090 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2090 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2090) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2090.1, data_15_2090.2]

/-- Complete interval computation for depth 15, residue 2091. -/
theorem bounds_15_2091 : exactInterval 15 2091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2091 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2091) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2091 : oddCount 2091 15 = 7 ∧ acceleratedOrbit 15 2091 = 140 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2091 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2091) = 3 ^ 7 * m + 140 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2091.1, data_15_2091.2]

/-- Complete interval computation for depth 15, residue 2092. -/
theorem bounds_15_2092 : exactInterval 15 2092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2092 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2092) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2092 : oddCount 2092 15 = 6 ∧ acceleratedOrbit 15 2092 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2092 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2092) = 3 ^ 6 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2092.1, data_15_2092.2]

/-- Complete interval computation for depth 15, residue 2093. -/
theorem bounds_15_2093 : exactInterval 15 2093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2093 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2093) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2093 : oddCount 2093 15 = 6 ∧ acceleratedOrbit 15 2093 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2093 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2093) = 3 ^ 6 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2093.1, data_15_2093.2]

/-- Complete interval computation for depth 15, residue 2094. -/
theorem bounds_15_2094 : exactInterval 15 2094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2094 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2094) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2094 : oddCount 2094 15 = 6 ∧ acceleratedOrbit 15 2094 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2094 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2094) = 3 ^ 6 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2094.1, data_15_2094.2]

/-- Complete interval computation for depth 15, residue 2095. -/
theorem bounds_15_2095 : exactInterval 15 2095 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2095 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2095) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2095 : oddCount 2095 15 = 10 ∧ acceleratedOrbit 15 2095 = 3779 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2095 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2095) = 3 ^ 10 * m + 3779 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2095.1, data_15_2095.2]

/-- Complete interval computation for depth 15, residue 2096. -/
theorem bounds_15_2096 : exactInterval 15 2096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2096 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2096) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2096 : oddCount 2096 15 = 5 ∧ acceleratedOrbit 15 2096 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2096 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2096) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2096.1, data_15_2096.2]

end Collatz.Research.PassageAtlas.Batch0064
