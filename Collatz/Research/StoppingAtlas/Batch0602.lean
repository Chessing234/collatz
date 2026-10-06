import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0602

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2063. -/
theorem bounds_13_2063 : exactInterval 13 2063 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2063 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2063) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2063 : oddCount 2063 13 = 6 ∧ acceleratedOrbit 13 2063 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2063 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2063) = 3 ^ 6 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2063.1, data_13_2063.2]

/-- Complete interval computation for depth 13, residue 2064. -/
theorem bounds_13_2064 : exactInterval 13 2064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2064 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2064) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2064 : oddCount 2064 13 = 6 ∧ acceleratedOrbit 13 2064 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2064 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2064) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2064.1, data_13_2064.2]

/-- Complete interval computation for depth 13, residue 2065. -/
theorem bounds_13_2065 : exactInterval 13 2065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2065 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2065) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2065 : oddCount 2065 13 = 5 ∧ acceleratedOrbit 13 2065 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2065 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2065) = 3 ^ 5 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2065.1, data_13_2065.2]

/-- Complete interval computation for depth 13, residue 2066. -/
theorem bounds_13_2066 : exactInterval 13 2066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2066 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2066) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2066 : oddCount 2066 13 = 7 ∧ acceleratedOrbit 13 2066 = 553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2066 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2066) = 3 ^ 7 * m + 553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2066.1, data_13_2066.2]

/-- Complete interval computation for depth 13, residue 2067. -/
theorem bounds_13_2067 : exactInterval 13 2067 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2067 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2067) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2067 : oddCount 2067 13 = 7 ∧ acceleratedOrbit 13 2067 = 553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2067 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2067) = 3 ^ 7 * m + 553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2067.1, data_13_2067.2]

/-- Complete interval computation for depth 13, residue 2068. -/
theorem bounds_13_2068 : exactInterval 13 2068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2068 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2068) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2068 : oddCount 2068 13 = 6 ∧ acceleratedOrbit 13 2068 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2068 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2068) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2068.1, data_13_2068.2]

/-- Complete interval computation for depth 13, residue 2069. -/
theorem bounds_13_2069 : exactInterval 13 2069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2069 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2069) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2069 : oddCount 2069 13 = 6 ∧ acceleratedOrbit 13 2069 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2069 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2069) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2069.1, data_13_2069.2]

/-- Complete interval computation for depth 13, residue 2070. -/
theorem bounds_13_2070 : exactInterval 13 2070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2070 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2070) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2070 : oddCount 2070 13 = 5 ∧ acceleratedOrbit 13 2070 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2070 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2070) = 3 ^ 5 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2070.1, data_13_2070.2]

/-- Complete interval computation for depth 13, residue 2071. -/
theorem bounds_13_2071 : exactInterval 13 2071 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2071 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2071) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2071 : oddCount 2071 13 = 5 ∧ acceleratedOrbit 13 2071 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2071 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2071) = 3 ^ 5 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2071.1, data_13_2071.2]

/-- Complete interval computation for depth 13, residue 2072. -/
theorem bounds_13_2072 : exactInterval 13 2072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2072 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2072) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2072 : oddCount 2072 13 = 6 ∧ acceleratedOrbit 13 2072 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2072 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2072) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2072.1, data_13_2072.2]

/-- Complete interval computation for depth 13, residue 2073. -/
theorem bounds_13_2073 : exactInterval 13 2073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2073 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2073) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2073 : oddCount 2073 13 = 8 ∧ acceleratedOrbit 13 2073 = 1664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2073 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2073) = 3 ^ 8 * m + 1664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2073.1, data_13_2073.2]

/-- Complete interval computation for depth 13, residue 2074. -/
theorem bounds_13_2074 : exactInterval 13 2074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2074 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2074) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2074 : oddCount 2074 13 = 6 ∧ acceleratedOrbit 13 2074 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2074 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2074) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2074.1, data_13_2074.2]

/-- Complete interval computation for depth 13, residue 2075. -/
theorem bounds_13_2075 : exactInterval 13 2075 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2075 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2075) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2075 : oddCount 2075 13 = 8 ∧ acceleratedOrbit 13 2075 = 1663 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2075 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2075) = 3 ^ 8 * m + 1663 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2075.1, data_13_2075.2]

/-- Complete interval computation for depth 13, residue 2076. -/
theorem bounds_13_2076 : exactInterval 13 2076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2076 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2076) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2076 : oddCount 2076 13 = 7 ∧ acceleratedOrbit 13 2076 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2076 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2076) = 3 ^ 7 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2076.1, data_13_2076.2]

/-- Complete interval computation for depth 13, residue 2077. -/
theorem bounds_13_2077 : exactInterval 13 2077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2077 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2077) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2077 : oddCount 2077 13 = 7 ∧ acceleratedOrbit 13 2077 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2077 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2077) = 3 ^ 7 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2077.1, data_13_2077.2]

end Collatz.Research.StoppingAtlas.Batch0602
