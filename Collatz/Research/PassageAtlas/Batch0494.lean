import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0494

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 16154. -/
theorem bounds_15_16154 : exactInterval 15 16154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16154 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16154) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16154 : oddCount 16154 15 = 5 ∧ acceleratedOrbit 15 16154 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16154 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16154) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16154.1, data_15_16154.2]

/-- Complete interval computation for depth 15, residue 16155. -/
theorem bounds_15_16155 : exactInterval 15 16155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16155 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16155) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16155 : oddCount 16155 15 = 12 ∧ acceleratedOrbit 15 16155 = 262030 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16155 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16155) = 3 ^ 12 * m + 262030 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16155.1, data_15_16155.2]

/-- Complete interval computation for depth 15, residue 16156. -/
theorem bounds_15_16156 : exactInterval 15 16156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16156 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16156) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16156 : oddCount 16156 15 = 9 ∧ acceleratedOrbit 15 16156 = 9710 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16156 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16156) = 3 ^ 9 * m + 9710 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16156.1, data_15_16156.2]

/-- Complete interval computation for depth 15, residue 16157. -/
theorem bounds_15_16157 : exactInterval 15 16157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16157 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16157) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16157 : oddCount 16157 15 = 9 ∧ acceleratedOrbit 15 16157 = 9710 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16157 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16157) = 3 ^ 9 * m + 9710 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16157.1, data_15_16157.2]

/-- Complete interval computation for depth 15, residue 16158. -/
theorem bounds_15_16158 : exactInterval 15 16158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16158 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16158) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16158 : oddCount 16158 15 = 9 ∧ acceleratedOrbit 15 16158 = 9710 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16158 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16158) = 3 ^ 9 * m + 9710 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16158.1, data_15_16158.2]

/-- Complete interval computation for depth 15, residue 16159. -/
theorem bounds_15_16159 : exactInterval 15 16159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16159 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16159) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16159 : oddCount 16159 15 = 10 ∧ acceleratedOrbit 15 16159 = 29123 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16159 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16159) = 3 ^ 10 * m + 29123 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16159.1, data_15_16159.2]

/-- Complete interval computation for depth 15, residue 16160. -/
theorem bounds_15_16160 : exactInterval 15 16160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16160 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16160) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16160 : oddCount 16160 15 = 6 ∧ acceleratedOrbit 15 16160 = 361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16160 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16160) = 3 ^ 6 * m + 361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16160.1, data_15_16160.2]

/-- Complete interval computation for depth 15, residue 16161. -/
theorem bounds_15_16161 : exactInterval 15 16161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16161 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16161) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16161 : oddCount 16161 15 = 8 ∧ acceleratedOrbit 15 16161 = 3239 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16161 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16161) = 3 ^ 8 * m + 3239 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16161.1, data_15_16161.2]

/-- Complete interval computation for depth 15, residue 16162. -/
theorem bounds_15_16162 : exactInterval 15 16162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16162 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16162) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16162 : oddCount 16162 15 = 9 ∧ acceleratedOrbit 15 16162 = 9719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16162 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16162) = 3 ^ 9 * m + 9719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16162.1, data_15_16162.2]

/-- Complete interval computation for depth 15, residue 16163. -/
theorem bounds_15_16163 : exactInterval 15 16163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16163 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16163) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16163 : oddCount 16163 15 = 9 ∧ acceleratedOrbit 15 16163 = 9719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16163 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16163) = 3 ^ 9 * m + 9719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16163.1, data_15_16163.2]

/-- Complete interval computation for depth 15, residue 16164. -/
theorem bounds_15_16164 : exactInterval 15 16164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16164 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16164) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16164 : oddCount 16164 15 = 9 ∧ acceleratedOrbit 15 16164 = 9719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16164 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16164) = 3 ^ 9 * m + 9719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16164.1, data_15_16164.2]

/-- Complete interval computation for depth 15, residue 16165. -/
theorem bounds_15_16165 : exactInterval 15 16165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16165 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16165) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16165 : oddCount 16165 15 = 9 ∧ acceleratedOrbit 15 16165 = 9719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16165 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16165) = 3 ^ 9 * m + 9719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16165.1, data_15_16165.2]

/-- Complete interval computation for depth 15, residue 16166. -/
theorem bounds_15_16166 : exactInterval 15 16166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16166 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16166) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16166 : oddCount 16166 15 = 9 ∧ acceleratedOrbit 15 16166 = 9719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16166 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16166) = 3 ^ 9 * m + 9719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16166.1, data_15_16166.2]

/-- Complete interval computation for depth 15, residue 16167. -/
theorem bounds_15_16167 : exactInterval 15 16167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16167 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16167) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16167 : oddCount 16167 15 = 9 ∧ acceleratedOrbit 15 16167 = 9713 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16167 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16167) = 3 ^ 9 * m + 9713 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16167.1, data_15_16167.2]

/-- Complete interval computation for depth 15, residue 16168. -/
theorem bounds_15_16168 : exactInterval 15 16168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16168 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16168) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16168 : oddCount 16168 15 = 6 ∧ acceleratedOrbit 15 16168 = 361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16168 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16168) = 3 ^ 6 * m + 361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16168.1, data_15_16168.2]

/-- Complete interval computation for depth 15, residue 16169. -/
theorem bounds_15_16169 : exactInterval 15 16169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16169 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16169) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16169 : oddCount 16169 15 = 8 ∧ acceleratedOrbit 15 16169 = 3239 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16169 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16169) = 3 ^ 8 * m + 3239 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16169.1, data_15_16169.2]

/-- Complete interval computation for depth 15, residue 16170. -/
theorem bounds_15_16170 : exactInterval 15 16170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16170 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16170) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16170 : oddCount 16170 15 = 6 ∧ acceleratedOrbit 15 16170 = 361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16170 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16170) = 3 ^ 6 * m + 361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16170.1, data_15_16170.2]

/-- Complete interval computation for depth 15, residue 16171. -/
theorem bounds_15_16171 : exactInterval 15 16171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16171 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16171) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16171 : oddCount 16171 15 = 9 ∧ acceleratedOrbit 15 16171 = 9719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16171 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16171) = 3 ^ 9 * m + 9719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16171.1, data_15_16171.2]

/-- Complete interval computation for depth 15, residue 16172. -/
theorem bounds_15_16172 : exactInterval 15 16172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16172 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16172) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16172 : oddCount 16172 15 = 4 ∧ acceleratedOrbit 15 16172 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16172 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16172) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16172.1, data_15_16172.2]

/-- Complete interval computation for depth 15, residue 16173. -/
theorem bounds_15_16173 : exactInterval 15 16173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16173 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16173) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16173 : oddCount 16173 15 = 4 ∧ acceleratedOrbit 15 16173 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16173 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16173) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16173.1, data_15_16173.2]

/-- Complete interval computation for depth 15, residue 16174. -/
theorem bounds_15_16174 : exactInterval 15 16174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16174 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16174) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16174 : oddCount 16174 15 = 4 ∧ acceleratedOrbit 15 16174 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16174 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16174) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16174.1, data_15_16174.2]

/-- Complete interval computation for depth 15, residue 16175. -/
theorem bounds_15_16175 : exactInterval 15 16175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16175 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16175) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16175 : oddCount 16175 15 = 9 ∧ acceleratedOrbit 15 16175 = 9719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16175 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16175) = 3 ^ 9 * m + 9719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16175.1, data_15_16175.2]

/-- Complete interval computation for depth 15, residue 16176. -/
theorem bounds_15_16176 : exactInterval 15 16176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16176 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16176) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16176 : oddCount 16176 15 = 6 ∧ acceleratedOrbit 15 16176 = 361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16176 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16176) = 3 ^ 6 * m + 361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16176.1, data_15_16176.2]

/-- Complete interval computation for depth 15, residue 16177. -/
theorem bounds_15_16177 : exactInterval 15 16177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16177 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16177) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16177 : oddCount 16177 15 = 4 ∧ acceleratedOrbit 15 16177 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16177 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16177) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16177.1, data_15_16177.2]

/-- Complete interval computation for depth 15, residue 16178. -/
theorem bounds_15_16178 : exactInterval 15 16178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16178 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16178) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16178 : oddCount 16178 15 = 4 ∧ acceleratedOrbit 15 16178 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16178 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16178) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16178.1, data_15_16178.2]

/-- Complete interval computation for depth 15, residue 16179. -/
theorem bounds_15_16179 : exactInterval 15 16179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16179 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16179) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16179 : oddCount 16179 15 = 4 ∧ acceleratedOrbit 15 16179 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16179 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16179) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16179.1, data_15_16179.2]

/-- Complete interval computation for depth 15, residue 16180. -/
theorem bounds_15_16180 : exactInterval 15 16180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16180 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16180) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16180 : oddCount 16180 15 = 6 ∧ acceleratedOrbit 15 16180 = 361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16180 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16180) = 3 ^ 6 * m + 361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16180.1, data_15_16180.2]

/-- Complete interval computation for depth 15, residue 16181. -/
theorem bounds_15_16181 : exactInterval 15 16181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16181 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16181) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16181 : oddCount 16181 15 = 6 ∧ acceleratedOrbit 15 16181 = 361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16181 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16181) = 3 ^ 6 * m + 361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16181.1, data_15_16181.2]

/-- Complete interval computation for depth 15, residue 16182. -/
theorem bounds_15_16182 : exactInterval 15 16182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16182 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16182) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16182 : oddCount 16182 15 = 8 ∧ acceleratedOrbit 15 16182 = 3241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16182 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16182) = 3 ^ 8 * m + 3241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16182.1, data_15_16182.2]

/-- Complete interval computation for depth 15, residue 16183. -/
theorem bounds_15_16183 : exactInterval 15 16183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16183 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16183) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16183 : oddCount 16183 15 = 8 ∧ acceleratedOrbit 15 16183 = 3241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16183 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16183) = 3 ^ 8 * m + 3241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16183.1, data_15_16183.2]

/-- Complete interval computation for depth 15, residue 16184. -/
theorem bounds_15_16184 : exactInterval 15 16184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16184 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16184) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16184 : oddCount 16184 15 = 7 ∧ acceleratedOrbit 15 16184 = 1081 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16184 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16184) = 3 ^ 7 * m + 1081 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16184.1, data_15_16184.2]

/-- Complete interval computation for depth 15, residue 16185. -/
theorem bounds_15_16185 : exactInterval 15 16185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16185 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16185) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16185 : oddCount 16185 15 = 8 ∧ acceleratedOrbit 15 16185 = 3242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16185 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16185) = 3 ^ 8 * m + 3242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16185.1, data_15_16185.2]

/-- Complete interval computation for depth 15, residue 16186. -/
theorem bounds_15_16186 : exactInterval 15 16186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16186 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16186) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16186 : oddCount 16186 15 = 7 ∧ acceleratedOrbit 15 16186 = 1081 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16186 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16186) = 3 ^ 7 * m + 1081 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16186.1, data_15_16186.2]

end Collatz.Research.PassageAtlas.Batch0494
