import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0803

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5150. -/
theorem bounds_13_5150 : exactInterval 13 5150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5150 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5150) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5150 : oddCount 5150 13 = 8 ∧ acceleratedOrbit 13 5150 = 4130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5150 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5150) = 3 ^ 8 * m + 4130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5150.1, data_13_5150.2]

/-- Complete interval computation for depth 13, residue 5151. -/
theorem bounds_13_5151 : exactInterval 13 5151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5151 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5151) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5151 : oddCount 5151 13 = 10 ∧ acceleratedOrbit 13 5151 = 37138 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5151 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5151) = 3 ^ 10 * m + 37138 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5151.1, data_13_5151.2]

/-- Complete interval computation for depth 13, residue 5152. -/
theorem bounds_13_5152 : exactInterval 13 5152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5152 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5152) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5152 : oddCount 5152 13 = 5 ∧ acceleratedOrbit 13 5152 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5152 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5152) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5152.1, data_13_5152.2]

/-- Complete interval computation for depth 13, residue 5153. -/
theorem bounds_13_5153 : exactInterval 13 5153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5153 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5153) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5153 : oddCount 5153 13 = 9 ∧ acceleratedOrbit 13 5153 = 12392 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5153 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5153) = 3 ^ 9 * m + 12392 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5153.1, data_13_5153.2]

/-- Complete interval computation for depth 13, residue 5154. -/
theorem bounds_13_5154 : exactInterval 13 5154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5154 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5154) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5154 : oddCount 5154 13 = 3 ∧ acceleratedOrbit 13 5154 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5154 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5154) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5154.1, data_13_5154.2]

/-- Complete interval computation for depth 13, residue 5155. -/
theorem bounds_13_5155 : exactInterval 13 5155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5155 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5155) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5155 : oddCount 5155 13 = 3 ∧ acceleratedOrbit 13 5155 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5155 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5155) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5155.1, data_13_5155.2]

/-- Complete interval computation for depth 13, residue 5156. -/
theorem bounds_13_5156 : exactInterval 13 5156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5156 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5156) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5156 : oddCount 5156 13 = 7 ∧ acceleratedOrbit 13 5156 = 1379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5156 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5156) = 3 ^ 7 * m + 1379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5156.1, data_13_5156.2]

/-- Complete interval computation for depth 13, residue 5157. -/
theorem bounds_13_5157 : exactInterval 13 5157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5157 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5157) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5157 : oddCount 5157 13 = 7 ∧ acceleratedOrbit 13 5157 = 1379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5157 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5157) = 3 ^ 7 * m + 1379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5157.1, data_13_5157.2]

/-- Complete interval computation for depth 13, residue 5158. -/
theorem bounds_13_5158 : exactInterval 13 5158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5158 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5158) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5158 : oddCount 5158 13 = 7 ∧ acceleratedOrbit 13 5158 = 1379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5158 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5158) = 3 ^ 7 * m + 1379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5158.1, data_13_5158.2]

/-- Complete interval computation for depth 13, residue 5159. -/
theorem bounds_13_5159 : exactInterval 13 5159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5159 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5159) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5159 : oddCount 5159 13 = 7 ∧ acceleratedOrbit 13 5159 = 1378 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5159 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5159) = 3 ^ 7 * m + 1378 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5159.1, data_13_5159.2]

/-- Complete interval computation for depth 13, residue 5160. -/
theorem bounds_13_5160 : exactInterval 13 5160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5160 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5160) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5160 : oddCount 5160 13 = 5 ∧ acceleratedOrbit 13 5160 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5160 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5160) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5160.1, data_13_5160.2]

/-- Complete interval computation for depth 13, residue 5161. -/
theorem bounds_13_5161 : exactInterval 13 5161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5161 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5161) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5161 : oddCount 5161 13 = 8 ∧ acceleratedOrbit 13 5161 = 4135 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5161 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5161) = 3 ^ 8 * m + 4135 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5161.1, data_13_5161.2]

/-- Complete interval computation for depth 13, residue 5162. -/
theorem bounds_13_5162 : exactInterval 13 5162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5162 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5162) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5162 : oddCount 5162 13 = 5 ∧ acceleratedOrbit 13 5162 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5162 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5162) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5162.1, data_13_5162.2]

/-- Complete interval computation for depth 13, residue 5163. -/
theorem bounds_13_5163 : exactInterval 13 5163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5163 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5163) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5163 : oddCount 5163 13 = 6 ∧ acceleratedOrbit 13 5163 = 460 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5163 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5163) = 3 ^ 6 * m + 460 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5163.1, data_13_5163.2]

/-- Complete interval computation for depth 13, residue 5164. -/
theorem bounds_13_5164 : exactInterval 13 5164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5164 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5164) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5164 : oddCount 5164 13 = 6 ∧ acceleratedOrbit 13 5164 = 461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5164 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5164) = 3 ^ 6 * m + 461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5164.1, data_13_5164.2]

/-- Complete interval computation for depth 13, residue 5165. -/
theorem bounds_13_5165 : exactInterval 13 5165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5165 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5165) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5165 : oddCount 5165 13 = 6 ∧ acceleratedOrbit 13 5165 = 461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5165 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5165) = 3 ^ 6 * m + 461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5165.1, data_13_5165.2]

end Collatz.Research.StoppingAtlas.Batch0803
