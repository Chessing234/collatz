import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0677

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 22151. -/
theorem bounds_15_22151 : exactInterval 15 22151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22151 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22151) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22151 : oddCount 22151 15 = 9 ∧ acceleratedOrbit 15 22151 = 13310 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22151 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22151) = 3 ^ 9 * m + 13310 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22151.1, data_15_22151.2]

/-- Complete interval computation for depth 15, residue 22152. -/
theorem bounds_15_22152 : exactInterval 15 22152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22152 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22152) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22152 : oddCount 22152 15 = 6 ∧ acceleratedOrbit 15 22152 = 494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22152 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22152) = 3 ^ 6 * m + 494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22152.1, data_15_22152.2]

/-- Complete interval computation for depth 15, residue 22153. -/
theorem bounds_15_22153 : exactInterval 15 22153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22153 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22153) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22153 : oddCount 22153 15 = 8 ∧ acceleratedOrbit 15 22153 = 4436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22153 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22153) = 3 ^ 8 * m + 4436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22153.1, data_15_22153.2]

/-- Complete interval computation for depth 15, residue 22154. -/
theorem bounds_15_22154 : exactInterval 15 22154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22154 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22154) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22154 : oddCount 22154 15 = 6 ∧ acceleratedOrbit 15 22154 = 494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22154 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22154) = 3 ^ 6 * m + 494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22154.1, data_15_22154.2]

/-- Complete interval computation for depth 15, residue 22155. -/
theorem bounds_15_22155 : exactInterval 15 22155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22155 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22155) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22155 : oddCount 22155 15 = 6 ∧ acceleratedOrbit 15 22155 = 493 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22155 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22155) = 3 ^ 6 * m + 493 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22155.1, data_15_22155.2]

/-- Complete interval computation for depth 15, residue 22156. -/
theorem bounds_15_22156 : exactInterval 15 22156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22156 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22156) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22156 : oddCount 22156 15 = 6 ∧ acceleratedOrbit 15 22156 = 494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22156 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22156) = 3 ^ 6 * m + 494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22156.1, data_15_22156.2]

/-- Complete interval computation for depth 15, residue 22157. -/
theorem bounds_15_22157 : exactInterval 15 22157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22157 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22157) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22157 : oddCount 22157 15 = 6 ∧ acceleratedOrbit 15 22157 = 494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22157 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22157) = 3 ^ 6 * m + 494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22157.1, data_15_22157.2]

/-- Complete interval computation for depth 15, residue 22158. -/
theorem bounds_15_22158 : exactInterval 15 22158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22158 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22158) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22158 : oddCount 22158 15 = 9 ∧ acceleratedOrbit 15 22158 = 13312 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22158 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22158) = 3 ^ 9 * m + 13312 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22158.1, data_15_22158.2]

/-- Complete interval computation for depth 15, residue 22159. -/
theorem bounds_15_22159 : exactInterval 15 22159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22159 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22159) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22159 : oddCount 22159 15 = 9 ∧ acceleratedOrbit 15 22159 = 13312 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22159 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22159) = 3 ^ 9 * m + 13312 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22159.1, data_15_22159.2]

/-- Complete interval computation for depth 15, residue 22160. -/
theorem bounds_15_22160 : exactInterval 15 22160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22160 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22160) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22160 : oddCount 22160 15 = 6 ∧ acceleratedOrbit 15 22160 = 494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22160 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22160) = 3 ^ 6 * m + 494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22160.1, data_15_22160.2]

/-- Complete interval computation for depth 15, residue 22161. -/
theorem bounds_15_22161 : exactInterval 15 22161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22161 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22161) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22161 : oddCount 22161 15 = 7 ∧ acceleratedOrbit 15 22161 = 1480 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22161 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22161) = 3 ^ 7 * m + 1480 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22161.1, data_15_22161.2]

/-- Complete interval computation for depth 15, residue 22162. -/
theorem bounds_15_22162 : exactInterval 15 22162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22162 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22162) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22162 : oddCount 22162 15 = 7 ∧ acceleratedOrbit 15 22162 = 1480 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22162 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22162) = 3 ^ 7 * m + 1480 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22162.1, data_15_22162.2]

/-- Complete interval computation for depth 15, residue 22163. -/
theorem bounds_15_22163 : exactInterval 15 22163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22163 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22163) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22163 : oddCount 22163 15 = 7 ∧ acceleratedOrbit 15 22163 = 1480 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22163 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22163) = 3 ^ 7 * m + 1480 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22163.1, data_15_22163.2]

/-- Complete interval computation for depth 15, residue 22164. -/
theorem bounds_15_22164 : exactInterval 15 22164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22164 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22164) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22164 : oddCount 22164 15 = 6 ∧ acceleratedOrbit 15 22164 = 494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22164 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22164) = 3 ^ 6 * m + 494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22164.1, data_15_22164.2]

/-- Complete interval computation for depth 15, residue 22165. -/
theorem bounds_15_22165 : exactInterval 15 22165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22165 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22165) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22165 : oddCount 22165 15 = 6 ∧ acceleratedOrbit 15 22165 = 494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22165 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22165) = 3 ^ 6 * m + 494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22165.1, data_15_22165.2]

/-- Complete interval computation for depth 15, residue 22166. -/
theorem bounds_15_22166 : exactInterval 15 22166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22166 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22166) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22166 : oddCount 22166 15 = 6 ∧ acceleratedOrbit 15 22166 = 494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22166 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22166) = 3 ^ 6 * m + 494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22166.1, data_15_22166.2]

/-- Complete interval computation for depth 15, residue 22167. -/
theorem bounds_15_22167 : exactInterval 15 22167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22167 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22167) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22167 : oddCount 22167 15 = 6 ∧ acceleratedOrbit 15 22167 = 494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22167 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22167) = 3 ^ 6 * m + 494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22167.1, data_15_22167.2]

/-- Complete interval computation for depth 15, residue 22168. -/
theorem bounds_15_22168 : exactInterval 15 22168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22168 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22168) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22168 : oddCount 22168 15 = 6 ∧ acceleratedOrbit 15 22168 = 494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22168 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22168) = 3 ^ 6 * m + 494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22168.1, data_15_22168.2]

/-- Complete interval computation for depth 15, residue 22169. -/
theorem bounds_15_22169 : exactInterval 15 22169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22169 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22169) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22169 : oddCount 22169 15 = 10 ∧ acceleratedOrbit 15 22169 = 39959 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22169 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22169) = 3 ^ 10 * m + 39959 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22169.1, data_15_22169.2]

/-- Complete interval computation for depth 15, residue 22170. -/
theorem bounds_15_22170 : exactInterval 15 22170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22170 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22170) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22170 : oddCount 22170 15 = 6 ∧ acceleratedOrbit 15 22170 = 494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22170 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22170) = 3 ^ 6 * m + 494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22170.1, data_15_22170.2]

/-- Complete interval computation for depth 15, residue 22171. -/
theorem bounds_15_22171 : exactInterval 15 22171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22171 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22171) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22171 : oddCount 22171 15 = 9 ∧ acceleratedOrbit 15 22171 = 13319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22171 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22171) = 3 ^ 9 * m + 13319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22171.1, data_15_22171.2]

/-- Complete interval computation for depth 15, residue 22172. -/
theorem bounds_15_22172 : exactInterval 15 22172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22172 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22172) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22172 : oddCount 22172 15 = 8 ∧ acceleratedOrbit 15 22172 = 4441 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22172 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22172) = 3 ^ 8 * m + 4441 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22172.1, data_15_22172.2]

/-- Complete interval computation for depth 15, residue 22173. -/
theorem bounds_15_22173 : exactInterval 15 22173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22173 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22173) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22173 : oddCount 22173 15 = 8 ∧ acceleratedOrbit 15 22173 = 4441 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22173 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22173) = 3 ^ 8 * m + 4441 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22173.1, data_15_22173.2]

/-- Complete interval computation for depth 15, residue 22174. -/
theorem bounds_15_22174 : exactInterval 15 22174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22174 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22174) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22174 : oddCount 22174 15 = 8 ∧ acceleratedOrbit 15 22174 = 4441 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22174 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22174) = 3 ^ 8 * m + 4441 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22174.1, data_15_22174.2]

/-- Complete interval computation for depth 15, residue 22175. -/
theorem bounds_15_22175 : exactInterval 15 22175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22175 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22175) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22175 : oddCount 22175 15 = 12 ∧ acceleratedOrbit 15 22175 = 359660 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22175 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22175) = 3 ^ 12 * m + 359660 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22175.1, data_15_22175.2]

/-- Complete interval computation for depth 15, residue 22176. -/
theorem bounds_15_22176 : exactInterval 15 22176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22176 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22176) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22176 : oddCount 22176 15 = 4 ∧ acceleratedOrbit 15 22176 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22176 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22176) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22176.1, data_15_22176.2]

/-- Complete interval computation for depth 15, residue 22177. -/
theorem bounds_15_22177 : exactInterval 15 22177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22177 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22177) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22177 : oddCount 22177 15 = 9 ∧ acceleratedOrbit 15 22177 = 13324 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22177 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22177) = 3 ^ 9 * m + 13324 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22177.1, data_15_22177.2]

/-- Complete interval computation for depth 15, residue 22178. -/
theorem bounds_15_22178 : exactInterval 15 22178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22178 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22178) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22178 : oddCount 22178 15 = 9 ∧ acceleratedOrbit 15 22178 = 13328 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22178 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22178) = 3 ^ 9 * m + 13328 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22178.1, data_15_22178.2]

/-- Complete interval computation for depth 15, residue 22179. -/
theorem bounds_15_22179 : exactInterval 15 22179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22179 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22179) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22179 : oddCount 22179 15 = 9 ∧ acceleratedOrbit 15 22179 = 13328 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22179 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22179) = 3 ^ 9 * m + 13328 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22179.1, data_15_22179.2]

/-- Complete interval computation for depth 15, residue 22180. -/
theorem bounds_15_22180 : exactInterval 15 22180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22180 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22180) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22180 : oddCount 22180 15 = 9 ∧ acceleratedOrbit 15 22180 = 13328 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22180 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22180) = 3 ^ 9 * m + 13328 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22180.1, data_15_22180.2]

/-- Complete interval computation for depth 15, residue 22181. -/
theorem bounds_15_22181 : exactInterval 15 22181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22181 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22181) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22181 : oddCount 22181 15 = 9 ∧ acceleratedOrbit 15 22181 = 13328 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22181 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22181) = 3 ^ 9 * m + 13328 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22181.1, data_15_22181.2]

/-- Complete interval computation for depth 15, residue 22182. -/
theorem bounds_15_22182 : exactInterval 15 22182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22182 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22182) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22182 : oddCount 22182 15 = 9 ∧ acceleratedOrbit 15 22182 = 13328 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22182 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22182) = 3 ^ 9 * m + 13328 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22182.1, data_15_22182.2]

end Collatz.Research.PassageAtlas.Batch0677
