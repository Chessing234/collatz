import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0433

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 14155. -/
theorem bounds_15_14155 : exactInterval 15 14155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14155 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14155) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14155 : oddCount 14155 15 = 4 ∧ acceleratedOrbit 15 14155 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14155 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14155) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14155.1, data_15_14155.2]

/-- Complete interval computation for depth 15, residue 14156. -/
theorem bounds_15_14156 : exactInterval 15 14156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14156 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14156) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14156 : oddCount 14156 15 = 8 ∧ acceleratedOrbit 15 14156 = 2837 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14156 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14156) = 3 ^ 8 * m + 2837 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14156.1, data_15_14156.2]

/-- Complete interval computation for depth 15, residue 14157. -/
theorem bounds_15_14157 : exactInterval 15 14157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14157 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14157) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14157 : oddCount 14157 15 = 8 ∧ acceleratedOrbit 15 14157 = 2837 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14157 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14157) = 3 ^ 8 * m + 2837 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14157.1, data_15_14157.2]

/-- Complete interval computation for depth 15, residue 14158. -/
theorem bounds_15_14158 : exactInterval 15 14158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14158 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14158) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14158 : oddCount 14158 15 = 9 ∧ acceleratedOrbit 15 14158 = 8507 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14158 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14158) = 3 ^ 9 * m + 8507 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14158.1, data_15_14158.2]

/-- Complete interval computation for depth 15, residue 14159. -/
theorem bounds_15_14159 : exactInterval 15 14159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14159 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14159) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14159 : oddCount 14159 15 = 9 ∧ acceleratedOrbit 15 14159 = 8507 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14159 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14159) = 3 ^ 9 * m + 8507 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14159.1, data_15_14159.2]

/-- Complete interval computation for depth 15, residue 14160. -/
theorem bounds_15_14160 : exactInterval 15 14160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14160 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14160) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14160 : oddCount 14160 15 = 5 ∧ acceleratedOrbit 15 14160 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14160 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14160) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14160.1, data_15_14160.2]

/-- Complete interval computation for depth 15, residue 14161. -/
theorem bounds_15_14161 : exactInterval 15 14161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14161 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14161) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14161 : oddCount 14161 15 = 8 ∧ acceleratedOrbit 15 14161 = 2837 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14161 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14161) = 3 ^ 8 * m + 2837 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14161.1, data_15_14161.2]

/-- Complete interval computation for depth 15, residue 14162. -/
theorem bounds_15_14162 : exactInterval 15 14162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14162 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14162) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14162 : oddCount 14162 15 = 9 ∧ acceleratedOrbit 15 14162 = 8509 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14162 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14162) = 3 ^ 9 * m + 8509 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14162.1, data_15_14162.2]

/-- Complete interval computation for depth 15, residue 14163. -/
theorem bounds_15_14163 : exactInterval 15 14163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14163 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14163) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14163 : oddCount 14163 15 = 9 ∧ acceleratedOrbit 15 14163 = 8509 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14163 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14163) = 3 ^ 9 * m + 8509 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14163.1, data_15_14163.2]

/-- Complete interval computation for depth 15, residue 14164. -/
theorem bounds_15_14164 : exactInterval 15 14164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14164 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14164) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14164 : oddCount 14164 15 = 5 ∧ acceleratedOrbit 15 14164 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14164 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14164) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14164.1, data_15_14164.2]

/-- Complete interval computation for depth 15, residue 14165. -/
theorem bounds_15_14165 : exactInterval 15 14165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14165 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14165) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14165 : oddCount 14165 15 = 5 ∧ acceleratedOrbit 15 14165 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14165 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14165) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14165.1, data_15_14165.2]

/-- Complete interval computation for depth 15, residue 14166. -/
theorem bounds_15_14166 : exactInterval 15 14166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14166 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14166) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14166 : oddCount 14166 15 = 7 ∧ acceleratedOrbit 15 14166 = 946 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14166 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14166) = 3 ^ 7 * m + 946 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14166.1, data_15_14166.2]

/-- Complete interval computation for depth 15, residue 14167. -/
theorem bounds_15_14167 : exactInterval 15 14167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14167 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14167) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14167 : oddCount 14167 15 = 7 ∧ acceleratedOrbit 15 14167 = 946 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14167 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14167) = 3 ^ 7 * m + 946 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14167.1, data_15_14167.2]

/-- Complete interval computation for depth 15, residue 14168. -/
theorem bounds_15_14168 : exactInterval 15 14168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14168 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14168) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14168 : oddCount 14168 15 = 7 ∧ acceleratedOrbit 15 14168 = 947 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14168 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14168) = 3 ^ 7 * m + 947 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14168.1, data_15_14168.2]

/-- Complete interval computation for depth 15, residue 14169. -/
theorem bounds_15_14169 : exactInterval 15 14169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14169 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14169) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14169 : oddCount 14169 15 = 7 ∧ acceleratedOrbit 15 14169 = 947 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14169 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14169) = 3 ^ 7 * m + 947 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14169.1, data_15_14169.2]

/-- Complete interval computation for depth 15, residue 14170. -/
theorem bounds_15_14170 : exactInterval 15 14170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14170 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14170) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14170 : oddCount 14170 15 = 7 ∧ acceleratedOrbit 15 14170 = 947 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14170 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14170) = 3 ^ 7 * m + 947 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14170.1, data_15_14170.2]

/-- Complete interval computation for depth 15, residue 14171. -/
theorem bounds_15_14171 : exactInterval 15 14171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14171 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14171) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14171 : oddCount 14171 15 = 10 ∧ acceleratedOrbit 15 14171 = 25541 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14171 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14171) = 3 ^ 10 * m + 25541 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14171.1, data_15_14171.2]

/-- Complete interval computation for depth 15, residue 14172. -/
theorem bounds_15_14172 : exactInterval 15 14172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14172 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14172) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14172 : oddCount 14172 15 = 7 ∧ acceleratedOrbit 15 14172 = 947 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14172 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14172) = 3 ^ 7 * m + 947 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14172.1, data_15_14172.2]

/-- Complete interval computation for depth 15, residue 14173. -/
theorem bounds_15_14173 : exactInterval 15 14173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14173 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14173) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14173 : oddCount 14173 15 = 7 ∧ acceleratedOrbit 15 14173 = 947 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14173 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14173) = 3 ^ 7 * m + 947 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14173.1, data_15_14173.2]

/-- Complete interval computation for depth 15, residue 14174. -/
theorem bounds_15_14174 : exactInterval 15 14174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14174 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14174) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14174 : oddCount 14174 15 = 7 ∧ acceleratedOrbit 15 14174 = 947 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14174 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14174) = 3 ^ 7 * m + 947 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14174.1, data_15_14174.2]

/-- Complete interval computation for depth 15, residue 14175. -/
theorem bounds_15_14175 : exactInterval 15 14175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14175 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14175) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14175 : oddCount 14175 15 = 7 ∧ acceleratedOrbit 15 14175 = 947 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14175 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14175) = 3 ^ 7 * m + 947 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14175.1, data_15_14175.2]

/-- Complete interval computation for depth 15, residue 14176. -/
theorem bounds_15_14176 : exactInterval 15 14176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14176 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14176) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14176 : oddCount 14176 15 = 6 ∧ acceleratedOrbit 15 14176 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14176 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14176) = 3 ^ 6 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14176.1, data_15_14176.2]

/-- Complete interval computation for depth 15, residue 14177. -/
theorem bounds_15_14177 : exactInterval 15 14177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14177 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14177) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14177 : oddCount 14177 15 = 9 ∧ acceleratedOrbit 15 14177 = 8518 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14177 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14177) = 3 ^ 9 * m + 8518 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14177.1, data_15_14177.2]

/-- Complete interval computation for depth 15, residue 14178. -/
theorem bounds_15_14178 : exactInterval 15 14178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14178 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14178) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14178 : oddCount 14178 15 = 6 ∧ acceleratedOrbit 15 14178 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14178 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14178) = 3 ^ 6 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14178.1, data_15_14178.2]

/-- Complete interval computation for depth 15, residue 14179. -/
theorem bounds_15_14179 : exactInterval 15 14179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14179 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14179) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14179 : oddCount 14179 15 = 6 ∧ acceleratedOrbit 15 14179 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14179 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14179) = 3 ^ 6 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14179.1, data_15_14179.2]

/-- Complete interval computation for depth 15, residue 14180. -/
theorem bounds_15_14180 : exactInterval 15 14180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14180 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14180) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14180 : oddCount 14180 15 = 6 ∧ acceleratedOrbit 15 14180 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14180 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14180) = 3 ^ 6 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14180.1, data_15_14180.2]

/-- Complete interval computation for depth 15, residue 14181. -/
theorem bounds_15_14181 : exactInterval 15 14181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14181 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14181) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14181 : oddCount 14181 15 = 6 ∧ acceleratedOrbit 15 14181 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14181 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14181) = 3 ^ 6 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14181.1, data_15_14181.2]

/-- Complete interval computation for depth 15, residue 14182. -/
theorem bounds_15_14182 : exactInterval 15 14182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14182 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14182) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14182 : oddCount 14182 15 = 6 ∧ acceleratedOrbit 15 14182 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14182 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14182) = 3 ^ 6 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14182.1, data_15_14182.2]

/-- Complete interval computation for depth 15, residue 14183. -/
theorem bounds_15_14183 : exactInterval 15 14183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14183 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14183) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14183 : oddCount 14183 15 = 11 ∧ acceleratedOrbit 15 14183 = 76682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14183 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14183) = 3 ^ 11 * m + 76682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14183.1, data_15_14183.2]

/-- Complete interval computation for depth 15, residue 14184. -/
theorem bounds_15_14184 : exactInterval 15 14184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14184 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14184) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14184 : oddCount 14184 15 = 6 ∧ acceleratedOrbit 15 14184 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14184 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14184) = 3 ^ 6 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14184.1, data_15_14184.2]

/-- Complete interval computation for depth 15, residue 14185. -/
theorem bounds_15_14185 : exactInterval 15 14185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14185 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14185) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14185 : oddCount 14185 15 = 7 ∧ acceleratedOrbit 15 14185 = 947 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14185 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14185) = 3 ^ 7 * m + 947 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14185.1, data_15_14185.2]

/-- Complete interval computation for depth 15, residue 14186. -/
theorem bounds_15_14186 : exactInterval 15 14186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14186 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14186) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14186 : oddCount 14186 15 = 6 ∧ acceleratedOrbit 15 14186 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14186 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14186) = 3 ^ 6 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14186.1, data_15_14186.2]

/-- Complete interval computation for depth 15, residue 14187. -/
theorem bounds_15_14187 : exactInterval 15 14187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14187 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14187) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14187 : oddCount 14187 15 = 9 ∧ acceleratedOrbit 15 14187 = 8525 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14187 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14187) = 3 ^ 9 * m + 8525 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14187.1, data_15_14187.2]

end Collatz.Research.PassageAtlas.Batch0433
