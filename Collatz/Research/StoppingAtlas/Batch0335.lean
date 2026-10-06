import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0335

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2058. -/
theorem bounds_12_2058 : exactInterval 12 2058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2058 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2058) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2058 : oddCount 2058 12 = 4 ∧ acceleratedOrbit 12 2058 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2058 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2058) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2058.1, data_12_2058.2]

/-- Complete interval computation for depth 12, residue 2059. -/
theorem bounds_12_2059 : exactInterval 12 2059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2059 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2059) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2059 : oddCount 2059 12 = 6 ∧ acceleratedOrbit 12 2059 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2059 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2059) = 3 ^ 6 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2059.1, data_12_2059.2]

/-- Complete interval computation for depth 12, residue 2060. -/
theorem bounds_12_2060 : exactInterval 12 2060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2060 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2060) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2060 : oddCount 2060 12 = 4 ∧ acceleratedOrbit 12 2060 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2060 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2060) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2060.1, data_12_2060.2]

/-- Complete interval computation for depth 12, residue 2061. -/
theorem bounds_12_2061 : exactInterval 12 2061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2061 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2061) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2061 : oddCount 2061 12 = 4 ∧ acceleratedOrbit 12 2061 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2061 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2061) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2061.1, data_12_2061.2]

/-- Complete interval computation for depth 12, residue 2062. -/
theorem bounds_12_2062 : exactInterval 12 2062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2062 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2062) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2062 : oddCount 2062 12 = 6 ∧ acceleratedOrbit 12 2062 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2062 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2062) = 3 ^ 6 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2062.1, data_12_2062.2]

/-- Complete interval computation for depth 12, residue 2063. -/
theorem bounds_12_2063 : exactInterval 12 2063 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2063 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2063) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2063 : oddCount 2063 12 = 6 ∧ acceleratedOrbit 12 2063 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2063 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2063) = 3 ^ 6 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2063.1, data_12_2063.2]

/-- Complete interval computation for depth 12, residue 2064. -/
theorem bounds_12_2064 : exactInterval 12 2064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2064 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2064) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2064 : oddCount 2064 12 = 5 ∧ acceleratedOrbit 12 2064 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2064 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2064) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2064.1, data_12_2064.2]

/-- Complete interval computation for depth 12, residue 2065. -/
theorem bounds_12_2065 : exactInterval 12 2065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2065 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2065) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2065 : oddCount 2065 12 = 4 ∧ acceleratedOrbit 12 2065 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2065 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2065) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2065.1, data_12_2065.2]

/-- Complete interval computation for depth 12, residue 2066. -/
theorem bounds_12_2066 : exactInterval 12 2066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2066 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2066) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2066 : oddCount 2066 12 = 7 ∧ acceleratedOrbit 12 2066 = 1106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2066 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2066) = 3 ^ 7 * m + 1106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2066.1, data_12_2066.2]

/-- Complete interval computation for depth 12, residue 2067. -/
theorem bounds_12_2067 : exactInterval 12 2067 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2067 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2067) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2067 : oddCount 2067 12 = 7 ∧ acceleratedOrbit 12 2067 = 1106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2067 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2067) = 3 ^ 7 * m + 1106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2067.1, data_12_2067.2]

/-- Complete interval computation for depth 12, residue 2068. -/
theorem bounds_12_2068 : exactInterval 12 2068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2068 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2068) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2068 : oddCount 2068 12 = 5 ∧ acceleratedOrbit 12 2068 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2068 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2068) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2068.1, data_12_2068.2]

/-- Complete interval computation for depth 12, residue 2069. -/
theorem bounds_12_2069 : exactInterval 12 2069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2069 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2069) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2069 : oddCount 2069 12 = 5 ∧ acceleratedOrbit 12 2069 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2069 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2069) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2069.1, data_12_2069.2]

/-- Complete interval computation for depth 12, residue 2070. -/
theorem bounds_12_2070 : exactInterval 12 2070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2070 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2070) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2070 : oddCount 2070 12 = 4 ∧ acceleratedOrbit 12 2070 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2070 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2070) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2070.1, data_12_2070.2]

/-- Complete interval computation for depth 12, residue 2071. -/
theorem bounds_12_2071 : exactInterval 12 2071 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2071 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2071) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2071 : oddCount 2071 12 = 4 ∧ acceleratedOrbit 12 2071 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2071 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2071) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2071.1, data_12_2071.2]

/-- Complete interval computation for depth 12, residue 2072. -/
theorem bounds_12_2072 : exactInterval 12 2072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2072 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2072) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2072 : oddCount 2072 12 = 5 ∧ acceleratedOrbit 12 2072 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2072 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2072) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2072.1, data_12_2072.2]

end Collatz.Research.StoppingAtlas.Batch0335
