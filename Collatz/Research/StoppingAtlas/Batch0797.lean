import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0797

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5058. -/
theorem bounds_13_5058 : exactInterval 13 5058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5058 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5058) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5058 : oddCount 5058 13 = 7 ∧ acceleratedOrbit 13 5058 = 1352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5058 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5058) = 3 ^ 7 * m + 1352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5058.1, data_13_5058.2]

/-- Complete interval computation for depth 13, residue 5059. -/
theorem bounds_13_5059 : exactInterval 13 5059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5059 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5059) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5059 : oddCount 5059 13 = 7 ∧ acceleratedOrbit 13 5059 = 1352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5059 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5059) = 3 ^ 7 * m + 1352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5059.1, data_13_5059.2]

/-- Complete interval computation for depth 13, residue 5060. -/
theorem bounds_13_5060 : exactInterval 13 5060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5060 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5060) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5060 : oddCount 5060 13 = 5 ∧ acceleratedOrbit 13 5060 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5060 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5060) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5060.1, data_13_5060.2]

/-- Complete interval computation for depth 13, residue 5061. -/
theorem bounds_13_5061 : exactInterval 13 5061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5061 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5061) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5061 : oddCount 5061 13 = 5 ∧ acceleratedOrbit 13 5061 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5061 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5061) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5061.1, data_13_5061.2]

/-- Complete interval computation for depth 13, residue 5062. -/
theorem bounds_13_5062 : exactInterval 13 5062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5062 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5062) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5062 : oddCount 5062 13 = 5 ∧ acceleratedOrbit 13 5062 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5062 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5062) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5062.1, data_13_5062.2]

/-- Complete interval computation for depth 13, residue 5063. -/
theorem bounds_13_5063 : exactInterval 13 5063 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5063 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5063) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5063 : oddCount 5063 13 = 9 ∧ acceleratedOrbit 13 5063 = 12170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5063 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5063) = 3 ^ 9 * m + 12170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5063.1, data_13_5063.2]

/-- Complete interval computation for depth 13, residue 5064. -/
theorem bounds_13_5064 : exactInterval 13 5064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5064 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5064) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5064 : oddCount 5064 13 = 6 ∧ acceleratedOrbit 13 5064 = 452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5064 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5064) = 3 ^ 6 * m + 452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5064.1, data_13_5064.2]

/-- Complete interval computation for depth 13, residue 5065. -/
theorem bounds_13_5065 : exactInterval 13 5065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5065 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5065) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5065 : oddCount 5065 13 = 6 ∧ acceleratedOrbit 13 5065 = 451 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5065 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5065) = 3 ^ 6 * m + 451 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5065.1, data_13_5065.2]

/-- Complete interval computation for depth 13, residue 5066. -/
theorem bounds_13_5066 : exactInterval 13 5066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5066 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5066) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5066 : oddCount 5066 13 = 6 ∧ acceleratedOrbit 13 5066 = 452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5066 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5066) = 3 ^ 6 * m + 452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5066.1, data_13_5066.2]

/-- Complete interval computation for depth 13, residue 5067. -/
theorem bounds_13_5067 : exactInterval 13 5067 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5067 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5067) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5067 : oddCount 5067 13 = 6 ∧ acceleratedOrbit 13 5067 = 452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5067 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5067) = 3 ^ 6 * m + 452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5067.1, data_13_5067.2]

/-- Complete interval computation for depth 13, residue 5068. -/
theorem bounds_13_5068 : exactInterval 13 5068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5068 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5068) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5068 : oddCount 5068 13 = 6 ∧ acceleratedOrbit 13 5068 = 452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5068 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5068) = 3 ^ 6 * m + 452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5068.1, data_13_5068.2]

/-- Complete interval computation for depth 13, residue 5069. -/
theorem bounds_13_5069 : exactInterval 13 5069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5069 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5069) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5069 : oddCount 5069 13 = 6 ∧ acceleratedOrbit 13 5069 = 452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5069 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5069) = 3 ^ 6 * m + 452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5069.1, data_13_5069.2]

/-- Complete interval computation for depth 13, residue 5070. -/
theorem bounds_13_5070 : exactInterval 13 5070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5070 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5070) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5070 : oddCount 5070 13 = 8 ∧ acceleratedOrbit 13 5070 = 4063 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5070 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5070) = 3 ^ 8 * m + 4063 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5070.1, data_13_5070.2]

/-- Complete interval computation for depth 13, residue 5071. -/
theorem bounds_13_5071 : exactInterval 13 5071 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5071 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5071) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5071 : oddCount 5071 13 = 8 ∧ acceleratedOrbit 13 5071 = 4063 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5071 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5071) = 3 ^ 8 * m + 4063 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5071.1, data_13_5071.2]

/-- Complete interval computation for depth 13, residue 5072. -/
theorem bounds_13_5072 : exactInterval 13 5072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5072 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5072) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5072 : oddCount 5072 13 = 5 ∧ acceleratedOrbit 13 5072 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5072 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5072) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5072.1, data_13_5072.2]

end Collatz.Research.StoppingAtlas.Batch0797
