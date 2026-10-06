import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0311

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 10158. -/
theorem bounds_15_10158 : exactInterval 15 10158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10158 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10158) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10158 : oddCount 10158 15 = 8 ∧ acceleratedOrbit 15 10158 = 2035 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10158 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10158) = 3 ^ 8 * m + 2035 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10158.1, data_15_10158.2]

/-- Complete interval computation for depth 15, residue 10159. -/
theorem bounds_15_10159 : exactInterval 15 10159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10159 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10159) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10159 : oddCount 10159 15 = 8 ∧ acceleratedOrbit 15 10159 = 2035 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10159 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10159) = 3 ^ 8 * m + 2035 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10159.1, data_15_10159.2]

/-- Complete interval computation for depth 15, residue 10160. -/
theorem bounds_15_10160 : exactInterval 15 10160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10160 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10160) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10160 : oddCount 10160 15 = 6 ∧ acceleratedOrbit 15 10160 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10160 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10160) = 3 ^ 6 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10160.1, data_15_10160.2]

/-- Complete interval computation for depth 15, residue 10161. -/
theorem bounds_15_10161 : exactInterval 15 10161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10161 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10161) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10161 : oddCount 10161 15 = 5 ∧ acceleratedOrbit 15 10161 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10161 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10161) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10161.1, data_15_10161.2]

/-- Complete interval computation for depth 15, residue 10162. -/
theorem bounds_15_10162 : exactInterval 15 10162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10162 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10162) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10162 : oddCount 10162 15 = 5 ∧ acceleratedOrbit 15 10162 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10162 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10162) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10162.1, data_15_10162.2]

/-- Complete interval computation for depth 15, residue 10163. -/
theorem bounds_15_10163 : exactInterval 15 10163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10163 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10163) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10163 : oddCount 10163 15 = 5 ∧ acceleratedOrbit 15 10163 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10163 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10163) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10163.1, data_15_10163.2]

/-- Complete interval computation for depth 15, residue 10164. -/
theorem bounds_15_10164 : exactInterval 15 10164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10164 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10164) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10164 : oddCount 10164 15 = 6 ∧ acceleratedOrbit 15 10164 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10164 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10164) = 3 ^ 6 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10164.1, data_15_10164.2]

/-- Complete interval computation for depth 15, residue 10165. -/
theorem bounds_15_10165 : exactInterval 15 10165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10165 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10165) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10165 : oddCount 10165 15 = 6 ∧ acceleratedOrbit 15 10165 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10165 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10165) = 3 ^ 6 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10165.1, data_15_10165.2]

/-- Complete interval computation for depth 15, residue 10166. -/
theorem bounds_15_10166 : exactInterval 15 10166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10166 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10166) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10166 : oddCount 10166 15 = 7 ∧ acceleratedOrbit 15 10166 = 679 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10166 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10166) = 3 ^ 7 * m + 679 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10166.1, data_15_10166.2]

/-- Complete interval computation for depth 15, residue 10167. -/
theorem bounds_15_10167 : exactInterval 15 10167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10167 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10167) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10167 : oddCount 10167 15 = 7 ∧ acceleratedOrbit 15 10167 = 679 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10167 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10167) = 3 ^ 7 * m + 679 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10167.1, data_15_10167.2]

/-- Complete interval computation for depth 15, residue 10168. -/
theorem bounds_15_10168 : exactInterval 15 10168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10168 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10168) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10168 : oddCount 10168 15 = 6 ∧ acceleratedOrbit 15 10168 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10168 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10168) = 3 ^ 6 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10168.1, data_15_10168.2]

/-- Complete interval computation for depth 15, residue 10169. -/
theorem bounds_15_10169 : exactInterval 15 10169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10169 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10169) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10169 : oddCount 10169 15 = 8 ∧ acceleratedOrbit 15 10169 = 2038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10169 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10169) = 3 ^ 8 * m + 2038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10169.1, data_15_10169.2]

/-- Complete interval computation for depth 15, residue 10170. -/
theorem bounds_15_10170 : exactInterval 15 10170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10170 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10170) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10170 : oddCount 10170 15 = 6 ∧ acceleratedOrbit 15 10170 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10170 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10170) = 3 ^ 6 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10170.1, data_15_10170.2]

/-- Complete interval computation for depth 15, residue 10171. -/
theorem bounds_15_10171 : exactInterval 15 10171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10171 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10171) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10171 : oddCount 10171 15 = 8 ∧ acceleratedOrbit 15 10171 = 2038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10171 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10171) = 3 ^ 8 * m + 2038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10171.1, data_15_10171.2]

/-- Complete interval computation for depth 15, residue 10172. -/
theorem bounds_15_10172 : exactInterval 15 10172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10172 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10172) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10172 : oddCount 10172 15 = 9 ∧ acceleratedOrbit 15 10172 = 6113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10172 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10172) = 3 ^ 9 * m + 6113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10172.1, data_15_10172.2]

/-- Complete interval computation for depth 15, residue 10173. -/
theorem bounds_15_10173 : exactInterval 15 10173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10173 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10173) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10173 : oddCount 10173 15 = 9 ∧ acceleratedOrbit 15 10173 = 6113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10173 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10173) = 3 ^ 9 * m + 6113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10173.1, data_15_10173.2]

/-- Complete interval computation for depth 15, residue 10174. -/
theorem bounds_15_10174 : exactInterval 15 10174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10174 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10174) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10174 : oddCount 10174 15 = 9 ∧ acceleratedOrbit 15 10174 = 6113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10174 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10174) = 3 ^ 9 * m + 6113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10174.1, data_15_10174.2]

/-- Complete interval computation for depth 15, residue 10175. -/
theorem bounds_15_10175 : exactInterval 15 10175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10175 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10175) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10175 : oddCount 10175 15 = 9 ∧ acceleratedOrbit 15 10175 = 6113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10175 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10175) = 3 ^ 9 * m + 6113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10175.1, data_15_10175.2]

/-- Complete interval computation for depth 15, residue 10176. -/
theorem bounds_15_10176 : exactInterval 15 10176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10176 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10176) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10176 : oddCount 10176 15 = 8 ∧ acceleratedOrbit 15 10176 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10176 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10176) = 3 ^ 8 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10176.1, data_15_10176.2]

/-- Complete interval computation for depth 15, residue 10177. -/
theorem bounds_15_10177 : exactInterval 15 10177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10177 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10177) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10177 : oddCount 10177 15 = 6 ∧ acceleratedOrbit 15 10177 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10177 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10177) = 3 ^ 6 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10177.1, data_15_10177.2]

/-- Complete interval computation for depth 15, residue 10178. -/
theorem bounds_15_10178 : exactInterval 15 10178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10178 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10178) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10178 : oddCount 10178 15 = 8 ∧ acceleratedOrbit 15 10178 = 2039 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10178 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10178) = 3 ^ 8 * m + 2039 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10178.1, data_15_10178.2]

/-- Complete interval computation for depth 15, residue 10179. -/
theorem bounds_15_10179 : exactInterval 15 10179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10179 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10179) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10179 : oddCount 10179 15 = 8 ∧ acceleratedOrbit 15 10179 = 2039 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10179 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10179) = 3 ^ 8 * m + 2039 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10179.1, data_15_10179.2]

/-- Complete interval computation for depth 15, residue 10180. -/
theorem bounds_15_10180 : exactInterval 15 10180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10180 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10180) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10180 : oddCount 10180 15 = 5 ∧ acceleratedOrbit 15 10180 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10180 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10180) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10180.1, data_15_10180.2]

/-- Complete interval computation for depth 15, residue 10181. -/
theorem bounds_15_10181 : exactInterval 15 10181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10181 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10181) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10181 : oddCount 10181 15 = 5 ∧ acceleratedOrbit 15 10181 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10181 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10181) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10181.1, data_15_10181.2]

/-- Complete interval computation for depth 15, residue 10182. -/
theorem bounds_15_10182 : exactInterval 15 10182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10182 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10182) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10182 : oddCount 10182 15 = 5 ∧ acceleratedOrbit 15 10182 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10182 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10182) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10182.1, data_15_10182.2]

/-- Complete interval computation for depth 15, residue 10183. -/
theorem bounds_15_10183 : exactInterval 15 10183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10183 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10183) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10183 : oddCount 10183 15 = 9 ∧ acceleratedOrbit 15 10183 = 6119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10183 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10183) = 3 ^ 9 * m + 6119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10183.1, data_15_10183.2]

/-- Complete interval computation for depth 15, residue 10184. -/
theorem bounds_15_10184 : exactInterval 15 10184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10184 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10184) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10184 : oddCount 10184 15 = 6 ∧ acceleratedOrbit 15 10184 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10184 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10184) = 3 ^ 6 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10184.1, data_15_10184.2]

/-- Complete interval computation for depth 15, residue 10185. -/
theorem bounds_15_10185 : exactInterval 15 10185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10185 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10185) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10185 : oddCount 10185 15 = 7 ∧ acceleratedOrbit 15 10185 = 680 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10185 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10185) = 3 ^ 7 * m + 680 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10185.1, data_15_10185.2]

/-- Complete interval computation for depth 15, residue 10186. -/
theorem bounds_15_10186 : exactInterval 15 10186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10186 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10186) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10186 : oddCount 10186 15 = 6 ∧ acceleratedOrbit 15 10186 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10186 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10186) = 3 ^ 6 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10186.1, data_15_10186.2]

/-- Complete interval computation for depth 15, residue 10187. -/
theorem bounds_15_10187 : exactInterval 15 10187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10187 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10187) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10187 : oddCount 10187 15 = 6 ∧ acceleratedOrbit 15 10187 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10187 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10187) = 3 ^ 6 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10187.1, data_15_10187.2]

/-- Complete interval computation for depth 15, residue 10188. -/
theorem bounds_15_10188 : exactInterval 15 10188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10188 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10188) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10188 : oddCount 10188 15 = 6 ∧ acceleratedOrbit 15 10188 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10188 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10188) = 3 ^ 6 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10188.1, data_15_10188.2]

/-- Complete interval computation for depth 15, residue 10189. -/
theorem bounds_15_10189 : exactInterval 15 10189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10189 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10189) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10189 : oddCount 10189 15 = 6 ∧ acceleratedOrbit 15 10189 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10189 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10189) = 3 ^ 6 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10189.1, data_15_10189.2]

end Collatz.Research.PassageAtlas.Batch0311
