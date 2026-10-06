import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0864

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6087. -/
theorem bounds_13_6087 : exactInterval 13 6087 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6087 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6087) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6087 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6087 : oddCount 6087 13 = 8 ∧ acceleratedOrbit 13 6087 = 4877 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6087 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6087) = 3 ^ 8 * m + 4877 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6087.1, data_13_6087.2]

/-- Complete interval computation for depth 13, residue 6088. -/
theorem bounds_13_6088 : exactInterval 13 6088 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6088 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6088) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6088 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6088 : oddCount 6088 13 = 5 ∧ acceleratedOrbit 13 6088 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6088 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6088) = 3 ^ 5 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6088.1, data_13_6088.2]

/-- Complete interval computation for depth 13, residue 6089. -/
theorem bounds_13_6089 : exactInterval 13 6089 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6089 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6089) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6089 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6089 : oddCount 6089 13 = 8 ∧ acceleratedOrbit 13 6089 = 4880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6089 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6089) = 3 ^ 8 * m + 4880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6089.1, data_13_6089.2]

/-- Complete interval computation for depth 13, residue 6090. -/
theorem bounds_13_6090 : exactInterval 13 6090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6090 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6090) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6090 : oddCount 6090 13 = 5 ∧ acceleratedOrbit 13 6090 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6090 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6090) = 3 ^ 5 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6090.1, data_13_6090.2]

/-- Complete interval computation for depth 13, residue 6091. -/
theorem bounds_13_6091 : exactInterval 13 6091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6091 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6091) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6091 : oddCount 6091 13 = 5 ∧ acceleratedOrbit 13 6091 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6091 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6091) = 3 ^ 5 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6091.1, data_13_6091.2]

/-- Complete interval computation for depth 13, residue 6092. -/
theorem bounds_13_6092 : exactInterval 13 6092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6092 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6092) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6092 : oddCount 6092 13 = 5 ∧ acceleratedOrbit 13 6092 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6092 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6092) = 3 ^ 5 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6092.1, data_13_6092.2]

/-- Complete interval computation for depth 13, residue 6093. -/
theorem bounds_13_6093 : exactInterval 13 6093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6093 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6093) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6093 : oddCount 6093 13 = 5 ∧ acceleratedOrbit 13 6093 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6093 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6093) = 3 ^ 5 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6093.1, data_13_6093.2]

/-- Complete interval computation for depth 13, residue 6094. -/
theorem bounds_13_6094 : exactInterval 13 6094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6094 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6094) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6094 : oddCount 6094 13 = 7 ∧ acceleratedOrbit 13 6094 = 1628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6094 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6094) = 3 ^ 7 * m + 1628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6094.1, data_13_6094.2]

/-- Complete interval computation for depth 13, residue 6095. -/
theorem bounds_13_6095 : exactInterval 13 6095 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6095 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6095) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6095 : oddCount 6095 13 = 7 ∧ acceleratedOrbit 13 6095 = 1628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6095 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6095) = 3 ^ 7 * m + 1628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6095.1, data_13_6095.2]

/-- Complete interval computation for depth 13, residue 6096. -/
theorem bounds_13_6096 : exactInterval 13 6096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6096 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6096) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6096 : oddCount 6096 13 = 5 ∧ acceleratedOrbit 13 6096 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6096 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6096) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6096.1, data_13_6096.2]

/-- Complete interval computation for depth 13, residue 6097. -/
theorem bounds_13_6097 : exactInterval 13 6097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6097 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6097) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6097 : oddCount 6097 13 = 5 ∧ acceleratedOrbit 13 6097 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6097 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6097) = 3 ^ 5 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6097.1, data_13_6097.2]

/-- Complete interval computation for depth 13, residue 6098. -/
theorem bounds_13_6098 : exactInterval 13 6098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6098 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6098) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6098 : oddCount 6098 13 = 10 ∧ acceleratedOrbit 13 6098 = 43982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6098 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6098) = 3 ^ 10 * m + 43982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6098.1, data_13_6098.2]

/-- Complete interval computation for depth 13, residue 6099. -/
theorem bounds_13_6099 : exactInterval 13 6099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6099 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6099) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6099 : oddCount 6099 13 = 10 ∧ acceleratedOrbit 13 6099 = 43982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6099 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6099) = 3 ^ 10 * m + 43982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6099.1, data_13_6099.2]

/-- Complete interval computation for depth 13, residue 6100. -/
theorem bounds_13_6100 : exactInterval 13 6100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6100 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6100) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6100 : oddCount 6100 13 = 5 ∧ acceleratedOrbit 13 6100 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6100 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6100) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6100.1, data_13_6100.2]

/-- Complete interval computation for depth 13, residue 6101. -/
theorem bounds_13_6101 : exactInterval 13 6101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6101 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6101) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6101 : oddCount 6101 13 = 5 ∧ acceleratedOrbit 13 6101 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6101 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6101) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6101.1, data_13_6101.2]

/-- Complete interval computation for depth 13, residue 6102. -/
theorem bounds_13_6102 : exactInterval 13 6102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6102 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6102) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6102 : oddCount 6102 13 = 7 ∧ acceleratedOrbit 13 6102 = 1630 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6102 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6102) = 3 ^ 7 * m + 1630 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6102.1, data_13_6102.2]

end Collatz.Research.StoppingAtlas.Batch0864
