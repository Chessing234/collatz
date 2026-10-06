import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0738

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4152. -/
theorem bounds_13_4152 : exactInterval 13 4152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4152 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4152) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4152 : oddCount 4152 13 = 6 ∧ acceleratedOrbit 13 4152 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4152 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4152) = 3 ^ 6 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4152.1, data_13_4152.2]

/-- Complete interval computation for depth 13, residue 4153. -/
theorem bounds_13_4153 : exactInterval 13 4153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4153 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4153) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4153 : oddCount 4153 13 = 6 ∧ acceleratedOrbit 13 4153 = 370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4153 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4153) = 3 ^ 6 * m + 370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4153.1, data_13_4153.2]

/-- Complete interval computation for depth 13, residue 4154. -/
theorem bounds_13_4154 : exactInterval 13 4154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4154 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4154) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4154 : oddCount 4154 13 = 6 ∧ acceleratedOrbit 13 4154 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4154 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4154) = 3 ^ 6 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4154.1, data_13_4154.2]

/-- Complete interval computation for depth 13, residue 4155. -/
theorem bounds_13_4155 : exactInterval 13 4155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4155 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4155) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4155 : oddCount 4155 13 = 6 ∧ acceleratedOrbit 13 4155 = 370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4155 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4155) = 3 ^ 6 * m + 370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4155.1, data_13_4155.2]

/-- Complete interval computation for depth 13, residue 4156. -/
theorem bounds_13_4156 : exactInterval 13 4156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4156 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4156) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4156 : oddCount 4156 13 = 6 ∧ acceleratedOrbit 13 4156 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4156 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4156) = 3 ^ 6 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4156.1, data_13_4156.2]

/-- Complete interval computation for depth 13, residue 4157. -/
theorem bounds_13_4157 : exactInterval 13 4157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4157 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4157) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4157 : oddCount 4157 13 = 6 ∧ acceleratedOrbit 13 4157 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4157 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4157) = 3 ^ 6 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4157.1, data_13_4157.2]

/-- Complete interval computation for depth 13, residue 4158. -/
theorem bounds_13_4158 : exactInterval 13 4158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4158 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4158) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4158 : oddCount 4158 13 = 8 ∧ acceleratedOrbit 13 4158 = 3332 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4158 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4158) = 3 ^ 8 * m + 3332 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4158.1, data_13_4158.2]

/-- Complete interval computation for depth 13, residue 4159. -/
theorem bounds_13_4159 : exactInterval 13 4159 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4159 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4159) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4159 : oddCount 4159 13 = 8 ∧ acceleratedOrbit 13 4159 = 3332 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4159 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4159) = 3 ^ 8 * m + 3332 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4159.1, data_13_4159.2]

/-- Complete interval computation for depth 13, residue 4160. -/
theorem bounds_13_4160 : exactInterval 13 4160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4160 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4160) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4160 : oddCount 4160 13 = 3 ∧ acceleratedOrbit 13 4160 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4160 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4160) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4160.1, data_13_4160.2]

/-- Complete interval computation for depth 13, residue 4161. -/
theorem bounds_13_4161 : exactInterval 13 4161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4161 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4161) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4161 : oddCount 4161 13 = 6 ∧ acceleratedOrbit 13 4161 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4161 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4161) = 3 ^ 6 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4161.1, data_13_4161.2]

/-- Complete interval computation for depth 13, residue 4162. -/
theorem bounds_13_4162 : exactInterval 13 4162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4162 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4162) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4162 : oddCount 4162 13 = 6 ∧ acceleratedOrbit 13 4162 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4162 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4162) = 3 ^ 6 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4162.1, data_13_4162.2]

/-- Complete interval computation for depth 13, residue 4163. -/
theorem bounds_13_4163 : exactInterval 13 4163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4163 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4163) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4163 : oddCount 4163 13 = 6 ∧ acceleratedOrbit 13 4163 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4163 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4163) = 3 ^ 6 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4163.1, data_13_4163.2]

/-- Complete interval computation for depth 13, residue 4164. -/
theorem bounds_13_4164 : exactInterval 13 4164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4164 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4164) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4164 : oddCount 4164 13 = 5 ∧ acceleratedOrbit 13 4164 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4164 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4164) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4164.1, data_13_4164.2]

/-- Complete interval computation for depth 13, residue 4165. -/
theorem bounds_13_4165 : exactInterval 13 4165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4165 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4165) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4165 : oddCount 4165 13 = 5 ∧ acceleratedOrbit 13 4165 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4165 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4165) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4165.1, data_13_4165.2]

/-- Complete interval computation for depth 13, residue 4166. -/
theorem bounds_13_4166 : exactInterval 13 4166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4166 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4166) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4166 : oddCount 4166 13 = 5 ∧ acceleratedOrbit 13 4166 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4166 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4166) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4166.1, data_13_4166.2]

end Collatz.Research.StoppingAtlas.Batch0738
