import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0158

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 5144. -/
theorem bounds_15_5144 : exactInterval 15 5144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5144 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5144) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5144 : oddCount 5144 15 = 4 ∧ acceleratedOrbit 15 5144 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5144 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5144) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5144.1, data_15_5144.2]

/-- Complete interval computation for depth 15, residue 5145. -/
theorem bounds_15_5145 : exactInterval 15 5145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5145 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5145) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5145 : oddCount 5145 15 = 8 ∧ acceleratedOrbit 15 5145 = 1031 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5145 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5145) = 3 ^ 8 * m + 1031 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5145.1, data_15_5145.2]

/-- Complete interval computation for depth 15, residue 5146. -/
theorem bounds_15_5146 : exactInterval 15 5146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5146 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5146) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5146 : oddCount 5146 15 = 4 ∧ acceleratedOrbit 15 5146 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5146 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5146) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5146.1, data_15_5146.2]

/-- Complete interval computation for depth 15, residue 5147. -/
theorem bounds_15_5147 : exactInterval 15 5147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5147 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5147) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5147 : oddCount 5147 15 = 12 ∧ acceleratedOrbit 15 5147 = 83501 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5147 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5147) = 3 ^ 12 * m + 83501 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5147.1, data_15_5147.2]

/-- Complete interval computation for depth 15, residue 5148. -/
theorem bounds_15_5148 : exactInterval 15 5148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5148 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5148) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5148 : oddCount 5148 15 = 9 ∧ acceleratedOrbit 15 5148 = 3098 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5148 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5148) = 3 ^ 9 * m + 3098 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5148.1, data_15_5148.2]

/-- Complete interval computation for depth 15, residue 5149. -/
theorem bounds_15_5149 : exactInterval 15 5149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5149 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5149) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5149 : oddCount 5149 15 = 9 ∧ acceleratedOrbit 15 5149 = 3098 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5149 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5149) = 3 ^ 9 * m + 3098 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5149.1, data_15_5149.2]

/-- Complete interval computation for depth 15, residue 5150. -/
theorem bounds_15_5150 : exactInterval 15 5150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5150 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5150) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5150 : oddCount 5150 15 = 9 ∧ acceleratedOrbit 15 5150 = 3098 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5150 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5150) = 3 ^ 9 * m + 3098 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5150.1, data_15_5150.2]

/-- Complete interval computation for depth 15, residue 5151. -/
theorem bounds_15_5151 : exactInterval 15 5151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5151 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5151) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5151 : oddCount 5151 15 = 11 ∧ acceleratedOrbit 15 5151 = 27854 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5151 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5151) = 3 ^ 11 * m + 27854 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5151.1, data_15_5151.2]

/-- Complete interval computation for depth 15, residue 5152. -/
theorem bounds_15_5152 : exactInterval 15 5152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5152 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5152) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5152 : oddCount 5152 15 = 7 ∧ acceleratedOrbit 15 5152 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5152 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5152) = 3 ^ 7 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5152.1, data_15_5152.2]

/-- Complete interval computation for depth 15, residue 5153. -/
theorem bounds_15_5153 : exactInterval 15 5153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5153 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5153) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5153 : oddCount 5153 15 = 9 ∧ acceleratedOrbit 15 5153 = 3098 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5153 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5153) = 3 ^ 9 * m + 3098 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5153.1, data_15_5153.2]

/-- Complete interval computation for depth 15, residue 5154. -/
theorem bounds_15_5154 : exactInterval 15 5154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5154 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5154) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5154 : oddCount 5154 15 = 4 ∧ acceleratedOrbit 15 5154 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5154 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5154) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5154.1, data_15_5154.2]

/-- Complete interval computation for depth 15, residue 5155. -/
theorem bounds_15_5155 : exactInterval 15 5155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5155 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5155) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5155 : oddCount 5155 15 = 4 ∧ acceleratedOrbit 15 5155 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5155 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5155) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5155.1, data_15_5155.2]

/-- Complete interval computation for depth 15, residue 5156. -/
theorem bounds_15_5156 : exactInterval 15 5156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5156 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5156) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5156 : oddCount 5156 15 = 9 ∧ acceleratedOrbit 15 5156 = 3104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5156 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5156) = 3 ^ 9 * m + 3104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5156.1, data_15_5156.2]

/-- Complete interval computation for depth 15, residue 5157. -/
theorem bounds_15_5157 : exactInterval 15 5157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5157 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5157) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5157 : oddCount 5157 15 = 9 ∧ acceleratedOrbit 15 5157 = 3104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5157 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5157) = 3 ^ 9 * m + 3104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5157.1, data_15_5157.2]

/-- Complete interval computation for depth 15, residue 5158. -/
theorem bounds_15_5158 : exactInterval 15 5158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5158 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5158) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5158 : oddCount 5158 15 = 9 ∧ acceleratedOrbit 15 5158 = 3104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5158 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5158) = 3 ^ 9 * m + 3104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5158.1, data_15_5158.2]

/-- Complete interval computation for depth 15, residue 5159. -/
theorem bounds_15_5159 : exactInterval 15 5159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5159 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5159) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5159 : oddCount 5159 15 = 8 ∧ acceleratedOrbit 15 5159 = 1034 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5159 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5159) = 3 ^ 8 * m + 1034 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5159.1, data_15_5159.2]

/-- Complete interval computation for depth 15, residue 5160. -/
theorem bounds_15_5160 : exactInterval 15 5160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5160 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5160) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5160 : oddCount 5160 15 = 7 ∧ acceleratedOrbit 15 5160 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5160 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5160) = 3 ^ 7 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5160.1, data_15_5160.2]

/-- Complete interval computation for depth 15, residue 5161. -/
theorem bounds_15_5161 : exactInterval 15 5161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5161 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5161) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5161 : oddCount 5161 15 = 10 ∧ acceleratedOrbit 15 5161 = 9305 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5161 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5161) = 3 ^ 10 * m + 9305 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5161.1, data_15_5161.2]

/-- Complete interval computation for depth 15, residue 5162. -/
theorem bounds_15_5162 : exactInterval 15 5162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5162 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5162) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5162 : oddCount 5162 15 = 7 ∧ acceleratedOrbit 15 5162 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5162 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5162) = 3 ^ 7 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5162.1, data_15_5162.2]

/-- Complete interval computation for depth 15, residue 5163. -/
theorem bounds_15_5163 : exactInterval 15 5163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5163 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5163) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5163 : oddCount 5163 15 = 6 ∧ acceleratedOrbit 15 5163 = 115 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5163 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5163) = 3 ^ 6 * m + 115 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5163.1, data_15_5163.2]

/-- Complete interval computation for depth 15, residue 5164. -/
theorem bounds_15_5164 : exactInterval 15 5164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5164 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5164) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5164 : oddCount 5164 15 = 7 ∧ acceleratedOrbit 15 5164 = 346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5164 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5164) = 3 ^ 7 * m + 346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5164.1, data_15_5164.2]

/-- Complete interval computation for depth 15, residue 5165. -/
theorem bounds_15_5165 : exactInterval 15 5165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5165 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5165) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5165 : oddCount 5165 15 = 7 ∧ acceleratedOrbit 15 5165 = 346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5165 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5165) = 3 ^ 7 * m + 346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5165.1, data_15_5165.2]

/-- Complete interval computation for depth 15, residue 5166. -/
theorem bounds_15_5166 : exactInterval 15 5166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5166 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5166) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5166 : oddCount 5166 15 = 7 ∧ acceleratedOrbit 15 5166 = 346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5166 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5166) = 3 ^ 7 * m + 346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5166.1, data_15_5166.2]

/-- Complete interval computation for depth 15, residue 5167. -/
theorem bounds_15_5167 : exactInterval 15 5167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5167 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5167) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5167 : oddCount 5167 15 = 11 ∧ acceleratedOrbit 15 5167 = 27944 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5167 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5167) = 3 ^ 11 * m + 27944 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5167.1, data_15_5167.2]

/-- Complete interval computation for depth 15, residue 5168. -/
theorem bounds_15_5168 : exactInterval 15 5168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5168 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5168) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5168 : oddCount 5168 15 = 7 ∧ acceleratedOrbit 15 5168 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5168 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5168) = 3 ^ 7 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5168.1, data_15_5168.2]

/-- Complete interval computation for depth 15, residue 5169. -/
theorem bounds_15_5169 : exactInterval 15 5169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5169 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5169) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5169 : oddCount 5169 15 = 7 ∧ acceleratedOrbit 15 5169 = 346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5169 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5169) = 3 ^ 7 * m + 346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5169.1, data_15_5169.2]

/-- Complete interval computation for depth 15, residue 5170. -/
theorem bounds_15_5170 : exactInterval 15 5170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5170 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5170) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5170 : oddCount 5170 15 = 7 ∧ acceleratedOrbit 15 5170 = 346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5170 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5170) = 3 ^ 7 * m + 346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5170.1, data_15_5170.2]

/-- Complete interval computation for depth 15, residue 5171. -/
theorem bounds_15_5171 : exactInterval 15 5171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5171 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5171) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5171 : oddCount 5171 15 = 7 ∧ acceleratedOrbit 15 5171 = 346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5171 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5171) = 3 ^ 7 * m + 346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5171.1, data_15_5171.2]

/-- Complete interval computation for depth 15, residue 5172. -/
theorem bounds_15_5172 : exactInterval 15 5172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5172 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5172) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5172 : oddCount 5172 15 = 7 ∧ acceleratedOrbit 15 5172 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5172 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5172) = 3 ^ 7 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5172.1, data_15_5172.2]

/-- Complete interval computation for depth 15, residue 5173. -/
theorem bounds_15_5173 : exactInterval 15 5173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5173 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5173) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5173 : oddCount 5173 15 = 7 ∧ acceleratedOrbit 15 5173 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5173 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5173) = 3 ^ 7 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5173.1, data_15_5173.2]

/-- Complete interval computation for depth 15, residue 5174. -/
theorem bounds_15_5174 : exactInterval 15 5174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5174 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5174) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5174 : oddCount 5174 15 = 8 ∧ acceleratedOrbit 15 5174 = 1037 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5174 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5174) = 3 ^ 8 * m + 1037 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5174.1, data_15_5174.2]

/-- Complete interval computation for depth 15, residue 5175. -/
theorem bounds_15_5175 : exactInterval 15 5175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5175 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5175) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5175 : oddCount 5175 15 = 8 ∧ acceleratedOrbit 15 5175 = 1037 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5175 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5175) = 3 ^ 8 * m + 1037 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5175.1, data_15_5175.2]

/-- Complete interval computation for depth 15, residue 5176. -/
theorem bounds_15_5176 : exactInterval 15 5176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5176 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5176) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5176 : oddCount 5176 15 = 6 ∧ acceleratedOrbit 15 5176 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5176 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5176) = 3 ^ 6 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5176.1, data_15_5176.2]

end Collatz.Research.PassageAtlas.Batch0158
