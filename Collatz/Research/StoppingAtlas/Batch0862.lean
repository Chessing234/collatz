import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0862

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6056. -/
theorem bounds_13_6056 : exactInterval 13 6056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6056 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6056) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6056 : oddCount 6056 13 = 5 ∧ acceleratedOrbit 13 6056 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6056 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6056) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6056.1, data_13_6056.2]

/-- Complete interval computation for depth 13, residue 6057. -/
theorem bounds_13_6057 : exactInterval 13 6057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6057 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6057) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6057 : oddCount 6057 13 = 10 ∧ acceleratedOrbit 13 6057 = 43672 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6057 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6057) = 3 ^ 10 * m + 43672 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6057.1, data_13_6057.2]

/-- Complete interval computation for depth 13, residue 6058. -/
theorem bounds_13_6058 : exactInterval 13 6058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6058 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6058) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6058 : oddCount 6058 13 = 5 ∧ acceleratedOrbit 13 6058 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6058 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6058) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6058.1, data_13_6058.2]

/-- Complete interval computation for depth 13, residue 6059. -/
theorem bounds_13_6059 : exactInterval 13 6059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6059 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6059) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6059 : oddCount 6059 13 = 8 ∧ acceleratedOrbit 13 6059 = 4855 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6059 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6059) = 3 ^ 8 * m + 4855 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6059.1, data_13_6059.2]

/-- Complete interval computation for depth 13, residue 6060. -/
theorem bounds_13_6060 : exactInterval 13 6060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6060 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6060) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6060 : oddCount 6060 13 = 9 ∧ acceleratedOrbit 13 6060 = 14579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6060 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6060) = 3 ^ 9 * m + 14579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6060.1, data_13_6060.2]

/-- Complete interval computation for depth 13, residue 6061. -/
theorem bounds_13_6061 : exactInterval 13 6061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6061 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6061) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6061 : oddCount 6061 13 = 9 ∧ acceleratedOrbit 13 6061 = 14579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6061 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6061) = 3 ^ 9 * m + 14579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6061.1, data_13_6061.2]

/-- Complete interval computation for depth 13, residue 6062. -/
theorem bounds_13_6062 : exactInterval 13 6062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6062 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6062) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6062 : oddCount 6062 13 = 9 ∧ acceleratedOrbit 13 6062 = 14579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6062 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6062) = 3 ^ 9 * m + 14579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6062.1, data_13_6062.2]

/-- Complete interval computation for depth 13, residue 6063. -/
theorem bounds_13_6063 : exactInterval 13 6063 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6063 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6063) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6063 : oddCount 6063 13 = 8 ∧ acceleratedOrbit 13 6063 = 4859 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6063 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6063) = 3 ^ 8 * m + 4859 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6063.1, data_13_6063.2]

/-- Complete interval computation for depth 13, residue 6064. -/
theorem bounds_13_6064 : exactInterval 13 6064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6064 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6064) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6064 : oddCount 6064 13 = 6 ∧ acceleratedOrbit 13 6064 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6064 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6064) = 3 ^ 6 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6064.1, data_13_6064.2]

/-- Complete interval computation for depth 13, residue 6065. -/
theorem bounds_13_6065 : exactInterval 13 6065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6065 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6065) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6065 : oddCount 6065 13 = 3 ∧ acceleratedOrbit 13 6065 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6065 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6065) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6065.1, data_13_6065.2]

/-- Complete interval computation for depth 13, residue 6066. -/
theorem bounds_13_6066 : exactInterval 13 6066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6066 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6066) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6066 : oddCount 6066 13 = 3 ∧ acceleratedOrbit 13 6066 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6066 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6066) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6066.1, data_13_6066.2]

/-- Complete interval computation for depth 13, residue 6067. -/
theorem bounds_13_6067 : exactInterval 13 6067 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6067 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6067) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6067 : oddCount 6067 13 = 3 ∧ acceleratedOrbit 13 6067 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6067 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6067) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6067.1, data_13_6067.2]

/-- Complete interval computation for depth 13, residue 6068. -/
theorem bounds_13_6068 : exactInterval 13 6068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6068 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6068) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6068 : oddCount 6068 13 = 6 ∧ acceleratedOrbit 13 6068 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6068 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6068) = 3 ^ 6 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6068.1, data_13_6068.2]

/-- Complete interval computation for depth 13, residue 6069. -/
theorem bounds_13_6069 : exactInterval 13 6069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6069 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6069) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6069 : oddCount 6069 13 = 6 ∧ acceleratedOrbit 13 6069 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6069 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6069) = 3 ^ 6 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6069.1, data_13_6069.2]

/-- Complete interval computation for depth 13, residue 6070. -/
theorem bounds_13_6070 : exactInterval 13 6070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6070 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6070) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6070 : oddCount 6070 13 = 7 ∧ acceleratedOrbit 13 6070 = 1622 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6070 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6070) = 3 ^ 7 * m + 1622 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6070.1, data_13_6070.2]

/-- Complete interval computation for depth 13, residue 6071. -/
theorem bounds_13_6071 : exactInterval 13 6071 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6071 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6071) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6071 : oddCount 6071 13 = 7 ∧ acceleratedOrbit 13 6071 = 1622 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6071 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6071) = 3 ^ 7 * m + 1622 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6071.1, data_13_6071.2]

end Collatz.Research.StoppingAtlas.Batch0862
