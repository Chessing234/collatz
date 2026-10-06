import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0952

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 31162. -/
theorem bounds_15_31162 : exactInterval 15 31162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31162 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31162) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31162 : oddCount 31162 15 = 7 ∧ acceleratedOrbit 15 31162 = 2081 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31162 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31162) = 3 ^ 7 * m + 2081 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31162.1, data_15_31162.2]

/-- Complete interval computation for depth 15, residue 31163. -/
theorem bounds_15_31163 : exactInterval 15 31163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31163 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31163) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31163 : oddCount 31163 15 = 9 ∧ acceleratedOrbit 15 31163 = 18721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31163 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31163) = 3 ^ 9 * m + 18721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31163.1, data_15_31163.2]

/-- Complete interval computation for depth 15, residue 31164. -/
theorem bounds_15_31164 : exactInterval 15 31164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31164 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31164) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31164 : oddCount 31164 15 = 8 ∧ acceleratedOrbit 15 31164 = 6241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31164 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31164) = 3 ^ 8 * m + 6241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31164.1, data_15_31164.2]

/-- Complete interval computation for depth 15, residue 31165. -/
theorem bounds_15_31165 : exactInterval 15 31165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31165 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31165) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31165 : oddCount 31165 15 = 8 ∧ acceleratedOrbit 15 31165 = 6241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31165 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31165) = 3 ^ 8 * m + 6241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31165.1, data_15_31165.2]

/-- Complete interval computation for depth 15, residue 31166. -/
theorem bounds_15_31166 : exactInterval 15 31166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31166 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31166) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31166 : oddCount 31166 15 = 8 ∧ acceleratedOrbit 15 31166 = 6241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31166 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31166) = 3 ^ 8 * m + 6241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31166.1, data_15_31166.2]

/-- Complete interval computation for depth 15, residue 31167. -/
theorem bounds_15_31167 : exactInterval 15 31167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31167 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31167) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31167 : oddCount 31167 15 = 13 ∧ acceleratedOrbit 15 31167 = 1516481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31167 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31167) = 3 ^ 13 * m + 1516481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31167.1, data_15_31167.2]

/-- Complete interval computation for depth 15, residue 31168. -/
theorem bounds_15_31168 : exactInterval 15 31168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31168 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31168) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31168 : oddCount 31168 15 = 6 ∧ acceleratedOrbit 15 31168 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31168 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31168) = 3 ^ 6 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31168.1, data_15_31168.2]

/-- Complete interval computation for depth 15, residue 31169. -/
theorem bounds_15_31169 : exactInterval 15 31169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31169 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31169) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31169 : oddCount 31169 15 = 8 ∧ acceleratedOrbit 15 31169 = 6242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31169 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31169) = 3 ^ 8 * m + 6242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31169.1, data_15_31169.2]

/-- Complete interval computation for depth 15, residue 31170. -/
theorem bounds_15_31170 : exactInterval 15 31170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31170 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31170) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31170 : oddCount 31170 15 = 8 ∧ acceleratedOrbit 15 31170 = 6242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31170 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31170) = 3 ^ 8 * m + 6242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31170.1, data_15_31170.2]

/-- Complete interval computation for depth 15, residue 31171. -/
theorem bounds_15_31171 : exactInterval 15 31171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31171 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31171) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31171 : oddCount 31171 15 = 8 ∧ acceleratedOrbit 15 31171 = 6242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31171 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31171) = 3 ^ 8 * m + 6242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31171.1, data_15_31171.2]

/-- Complete interval computation for depth 15, residue 31172. -/
theorem bounds_15_31172 : exactInterval 15 31172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31172 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31172) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31172 : oddCount 31172 15 = 5 ∧ acceleratedOrbit 15 31172 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31172 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31172) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31172.1, data_15_31172.2]

/-- Complete interval computation for depth 15, residue 31173. -/
theorem bounds_15_31173 : exactInterval 15 31173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31173 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31173) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31173 : oddCount 31173 15 = 5 ∧ acceleratedOrbit 15 31173 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31173 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31173) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31173.1, data_15_31173.2]

/-- Complete interval computation for depth 15, residue 31174. -/
theorem bounds_15_31174 : exactInterval 15 31174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31174 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31174) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31174 : oddCount 31174 15 = 5 ∧ acceleratedOrbit 15 31174 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31174 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31174) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31174.1, data_15_31174.2]

/-- Complete interval computation for depth 15, residue 31175. -/
theorem bounds_15_31175 : exactInterval 15 31175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31175 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31175) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31175 : oddCount 31175 15 = 9 ∧ acceleratedOrbit 15 31175 = 18728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31175 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31175) = 3 ^ 9 * m + 18728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31175.1, data_15_31175.2]

/-- Complete interval computation for depth 15, residue 31176. -/
theorem bounds_15_31176 : exactInterval 15 31176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31176 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31176) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31176 : oddCount 31176 15 = 6 ∧ acceleratedOrbit 15 31176 = 694 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31176 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31176) = 3 ^ 6 * m + 694 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31176.1, data_15_31176.2]

/-- Complete interval computation for depth 15, residue 31177. -/
theorem bounds_15_31177 : exactInterval 15 31177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31177 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31177) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31177 : oddCount 31177 15 = 9 ∧ acceleratedOrbit 15 31177 = 18731 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31177 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31177) = 3 ^ 9 * m + 18731 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31177.1, data_15_31177.2]

/-- Complete interval computation for depth 15, residue 31178. -/
theorem bounds_15_31178 : exactInterval 15 31178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31178 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31178) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31178 : oddCount 31178 15 = 6 ∧ acceleratedOrbit 15 31178 = 694 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31178 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31178) = 3 ^ 6 * m + 694 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31178.1, data_15_31178.2]

/-- Complete interval computation for depth 15, residue 31179. -/
theorem bounds_15_31179 : exactInterval 15 31179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31179 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31179) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31179 : oddCount 31179 15 = 6 ∧ acceleratedOrbit 15 31179 = 694 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31179 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31179) = 3 ^ 6 * m + 694 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31179.1, data_15_31179.2]

/-- Complete interval computation for depth 15, residue 31180. -/
theorem bounds_15_31180 : exactInterval 15 31180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31180 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31180) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31180 : oddCount 31180 15 = 6 ∧ acceleratedOrbit 15 31180 = 694 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31180 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31180) = 3 ^ 6 * m + 694 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31180.1, data_15_31180.2]

/-- Complete interval computation for depth 15, residue 31181. -/
theorem bounds_15_31181 : exactInterval 15 31181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31181 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31181) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31181 : oddCount 31181 15 = 6 ∧ acceleratedOrbit 15 31181 = 694 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31181 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31181) = 3 ^ 6 * m + 694 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31181.1, data_15_31181.2]

/-- Complete interval computation for depth 15, residue 31182. -/
theorem bounds_15_31182 : exactInterval 15 31182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31182 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31182) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31182 : oddCount 31182 15 = 8 ∧ acceleratedOrbit 15 31182 = 6244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31182 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31182) = 3 ^ 8 * m + 6244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31182.1, data_15_31182.2]

/-- Complete interval computation for depth 15, residue 31183. -/
theorem bounds_15_31183 : exactInterval 15 31183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31183 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31183) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31183 : oddCount 31183 15 = 8 ∧ acceleratedOrbit 15 31183 = 6244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31183 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31183) = 3 ^ 8 * m + 6244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31183.1, data_15_31183.2]

/-- Complete interval computation for depth 15, residue 31184. -/
theorem bounds_15_31184 : exactInterval 15 31184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31184 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31184) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31184 : oddCount 31184 15 = 6 ∧ acceleratedOrbit 15 31184 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31184 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31184) = 3 ^ 6 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31184.1, data_15_31184.2]

/-- Complete interval computation for depth 15, residue 31185. -/
theorem bounds_15_31185 : exactInterval 15 31185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31185 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31185) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31185 : oddCount 31185 15 = 6 ∧ acceleratedOrbit 15 31185 = 694 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31185 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31185) = 3 ^ 6 * m + 694 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31185.1, data_15_31185.2]

/-- Complete interval computation for depth 15, residue 31186. -/
theorem bounds_15_31186 : exactInterval 15 31186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31186 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31186) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31186 : oddCount 31186 15 = 9 ∧ acceleratedOrbit 15 31186 = 18737 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31186 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31186) = 3 ^ 9 * m + 18737 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31186.1, data_15_31186.2]

/-- Complete interval computation for depth 15, residue 31187. -/
theorem bounds_15_31187 : exactInterval 15 31187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31187 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31187) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31187 : oddCount 31187 15 = 9 ∧ acceleratedOrbit 15 31187 = 18737 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31187 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31187) = 3 ^ 9 * m + 18737 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31187.1, data_15_31187.2]

/-- Complete interval computation for depth 15, residue 31188. -/
theorem bounds_15_31188 : exactInterval 15 31188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31188 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31188) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31188 : oddCount 31188 15 = 6 ∧ acceleratedOrbit 15 31188 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31188 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31188) = 3 ^ 6 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31188.1, data_15_31188.2]

/-- Complete interval computation for depth 15, residue 31189. -/
theorem bounds_15_31189 : exactInterval 15 31189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31189 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31189) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31189 : oddCount 31189 15 = 6 ∧ acceleratedOrbit 15 31189 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31189 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31189) = 3 ^ 6 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31189.1, data_15_31189.2]

/-- Complete interval computation for depth 15, residue 31190. -/
theorem bounds_15_31190 : exactInterval 15 31190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31190 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31190) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31190 : oddCount 31190 15 = 11 ∧ acceleratedOrbit 15 31190 = 168641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31190 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31190) = 3 ^ 11 * m + 168641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31190.1, data_15_31190.2]

/-- Complete interval computation for depth 15, residue 31191. -/
theorem bounds_15_31191 : exactInterval 15 31191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31191 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31191) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31191 : oddCount 31191 15 = 11 ∧ acceleratedOrbit 15 31191 = 168641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31191 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31191) = 3 ^ 11 * m + 168641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31191.1, data_15_31191.2]

/-- Complete interval computation for depth 15, residue 31192. -/
theorem bounds_15_31192 : exactInterval 15 31192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31192 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31192) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31192 : oddCount 31192 15 = 6 ∧ acceleratedOrbit 15 31192 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31192 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31192) = 3 ^ 6 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31192.1, data_15_31192.2]

/-- Complete interval computation for depth 15, residue 31193. -/
theorem bounds_15_31193 : exactInterval 15 31193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31193 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31193) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31193 : oddCount 31193 15 = 6 ∧ acceleratedOrbit 15 31193 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31193 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31193) = 3 ^ 6 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31193.1, data_15_31193.2]

/-- Complete interval computation for depth 15, residue 31194. -/
theorem bounds_15_31194 : exactInterval 15 31194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31194 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31194) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31194 : oddCount 31194 15 = 6 ∧ acceleratedOrbit 15 31194 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31194 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31194) = 3 ^ 6 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31194.1, data_15_31194.2]

end Collatz.Research.PassageAtlas.Batch0952
