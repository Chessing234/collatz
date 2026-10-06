import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0189

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 6160. -/
theorem bounds_15_6160 : exactInterval 15 6160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6160 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6160) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6160 : oddCount 6160 15 = 5 ∧ acceleratedOrbit 15 6160 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6160 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6160) = 3 ^ 5 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6160.1, data_15_6160.2]

/-- Complete interval computation for depth 15, residue 6161. -/
theorem bounds_15_6161 : exactInterval 15 6161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6161 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6161) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6161 : oddCount 6161 15 = 5 ∧ acceleratedOrbit 15 6161 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6161 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6161) = 3 ^ 5 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6161.1, data_15_6161.2]

/-- Complete interval computation for depth 15, residue 6162. -/
theorem bounds_15_6162 : exactInterval 15 6162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6162 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6162) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6162 : oddCount 6162 15 = 8 ∧ acceleratedOrbit 15 6162 = 1235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6162 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6162) = 3 ^ 8 * m + 1235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6162.1, data_15_6162.2]

/-- Complete interval computation for depth 15, residue 6163. -/
theorem bounds_15_6163 : exactInterval 15 6163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6163 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6163) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6163 : oddCount 6163 15 = 8 ∧ acceleratedOrbit 15 6163 = 1235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6163 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6163) = 3 ^ 8 * m + 1235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6163.1, data_15_6163.2]

/-- Complete interval computation for depth 15, residue 6164. -/
theorem bounds_15_6164 : exactInterval 15 6164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6164 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6164) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6164 : oddCount 6164 15 = 5 ∧ acceleratedOrbit 15 6164 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6164 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6164) = 3 ^ 5 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6164.1, data_15_6164.2]

/-- Complete interval computation for depth 15, residue 6165. -/
theorem bounds_15_6165 : exactInterval 15 6165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6165 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6165) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6165 : oddCount 6165 15 = 5 ∧ acceleratedOrbit 15 6165 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6165 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6165) = 3 ^ 5 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6165.1, data_15_6165.2]

/-- Complete interval computation for depth 15, residue 6166. -/
theorem bounds_15_6166 : exactInterval 15 6166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6166 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6166) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6166 : oddCount 6166 15 = 5 ∧ acceleratedOrbit 15 6166 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6166 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6166) = 3 ^ 5 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6166.1, data_15_6166.2]

/-- Complete interval computation for depth 15, residue 6167. -/
theorem bounds_15_6167 : exactInterval 15 6167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6167 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6167) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6167 : oddCount 6167 15 = 5 ∧ acceleratedOrbit 15 6167 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6167 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6167) = 3 ^ 5 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6167.1, data_15_6167.2]

/-- Complete interval computation for depth 15, residue 6168. -/
theorem bounds_15_6168 : exactInterval 15 6168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6168 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6168) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6168 : oddCount 6168 15 = 5 ∧ acceleratedOrbit 15 6168 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6168 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6168) = 3 ^ 5 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6168.1, data_15_6168.2]

/-- Complete interval computation for depth 15, residue 6169. -/
theorem bounds_15_6169 : exactInterval 15 6169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6169 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6169) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6169 : oddCount 6169 15 = 7 ∧ acceleratedOrbit 15 6169 = 412 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6169 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6169) = 3 ^ 7 * m + 412 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6169.1, data_15_6169.2]

/-- Complete interval computation for depth 15, residue 6170. -/
theorem bounds_15_6170 : exactInterval 15 6170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6170 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6170) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6170 : oddCount 6170 15 = 5 ∧ acceleratedOrbit 15 6170 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6170 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6170) = 3 ^ 5 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6170.1, data_15_6170.2]

/-- Complete interval computation for depth 15, residue 6171. -/
theorem bounds_15_6171 : exactInterval 15 6171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6171 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6171) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6171 : oddCount 6171 15 = 11 ∧ acceleratedOrbit 15 6171 = 33371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6171 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6171) = 3 ^ 11 * m + 33371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6171.1, data_15_6171.2]

/-- Complete interval computation for depth 15, residue 6172. -/
theorem bounds_15_6172 : exactInterval 15 6172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6172 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6172) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6172 : oddCount 6172 15 = 7 ∧ acceleratedOrbit 15 6172 = 413 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6172 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6172) = 3 ^ 7 * m + 413 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6172.1, data_15_6172.2]

/-- Complete interval computation for depth 15, residue 6173. -/
theorem bounds_15_6173 : exactInterval 15 6173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6173 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6173) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6173 : oddCount 6173 15 = 7 ∧ acceleratedOrbit 15 6173 = 413 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6173 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6173) = 3 ^ 7 * m + 413 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6173.1, data_15_6173.2]

/-- Complete interval computation for depth 15, residue 6174. -/
theorem bounds_15_6174 : exactInterval 15 6174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6174 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6174) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6174 : oddCount 6174 15 = 7 ∧ acceleratedOrbit 15 6174 = 413 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6174 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6174) = 3 ^ 7 * m + 413 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6174.1, data_15_6174.2]

/-- Complete interval computation for depth 15, residue 6175. -/
theorem bounds_15_6175 : exactInterval 15 6175 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6175 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6175) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6175 : oddCount 6175 15 = 9 ∧ acceleratedOrbit 15 6175 = 3710 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6175 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6175) = 3 ^ 9 * m + 3710 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6175.1, data_15_6175.2]

/-- Complete interval computation for depth 15, residue 6176. -/
theorem bounds_15_6176 : exactInterval 15 6176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6176 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6176) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6176 : oddCount 6176 15 = 5 ∧ acceleratedOrbit 15 6176 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6176 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6176) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6176.1, data_15_6176.2]

/-- Complete interval computation for depth 15, residue 6177. -/
theorem bounds_15_6177 : exactInterval 15 6177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6177 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6177) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6177 : oddCount 6177 15 = 7 ∧ acceleratedOrbit 15 6177 = 413 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6177 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6177) = 3 ^ 7 * m + 413 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6177.1, data_15_6177.2]

/-- Complete interval computation for depth 15, residue 6178. -/
theorem bounds_15_6178 : exactInterval 15 6178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6178 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6178) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6178 : oddCount 6178 15 = 5 ∧ acceleratedOrbit 15 6178 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6178 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6178) = 3 ^ 5 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6178.1, data_15_6178.2]

/-- Complete interval computation for depth 15, residue 6179. -/
theorem bounds_15_6179 : exactInterval 15 6179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6179 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6179) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6179 : oddCount 6179 15 = 5 ∧ acceleratedOrbit 15 6179 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6179 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6179) = 3 ^ 5 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6179.1, data_15_6179.2]

/-- Complete interval computation for depth 15, residue 6180. -/
theorem bounds_15_6180 : exactInterval 15 6180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6180 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6180) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6180 : oddCount 6180 15 = 8 ∧ acceleratedOrbit 15 6180 = 1241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6180 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6180) = 3 ^ 8 * m + 1241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6180.1, data_15_6180.2]

/-- Complete interval computation for depth 15, residue 6181. -/
theorem bounds_15_6181 : exactInterval 15 6181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6181 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6181) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6181 : oddCount 6181 15 = 8 ∧ acceleratedOrbit 15 6181 = 1241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6181 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6181) = 3 ^ 8 * m + 1241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6181.1, data_15_6181.2]

/-- Complete interval computation for depth 15, residue 6182. -/
theorem bounds_15_6182 : exactInterval 15 6182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6182 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6182) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6182 : oddCount 6182 15 = 8 ∧ acceleratedOrbit 15 6182 = 1241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6182 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6182) = 3 ^ 8 * m + 1241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6182.1, data_15_6182.2]

/-- Complete interval computation for depth 15, residue 6183. -/
theorem bounds_15_6183 : exactInterval 15 6183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6183 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6183) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6183 : oddCount 6183 15 = 9 ∧ acceleratedOrbit 15 6183 = 3716 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6183 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6183) = 3 ^ 9 * m + 3716 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6183.1, data_15_6183.2]

/-- Complete interval computation for depth 15, residue 6184. -/
theorem bounds_15_6184 : exactInterval 15 6184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6184 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6184) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6184 : oddCount 6184 15 = 5 ∧ acceleratedOrbit 15 6184 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6184 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6184) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6184.1, data_15_6184.2]

/-- Complete interval computation for depth 15, residue 6185. -/
theorem bounds_15_6185 : exactInterval 15 6185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6185 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6185) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6185 : oddCount 6185 15 = 10 ∧ acceleratedOrbit 15 6185 = 11150 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6185 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6185) = 3 ^ 10 * m + 11150 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6185.1, data_15_6185.2]

/-- Complete interval computation for depth 15, residue 6186. -/
theorem bounds_15_6186 : exactInterval 15 6186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6186 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6186) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6186 : oddCount 6186 15 = 5 ∧ acceleratedOrbit 15 6186 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6186 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6186) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6186.1, data_15_6186.2]

/-- Complete interval computation for depth 15, residue 6187. -/
theorem bounds_15_6187 : exactInterval 15 6187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6187 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6187) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6187 : oddCount 6187 15 = 8 ∧ acceleratedOrbit 15 6187 = 1241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6187 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6187) = 3 ^ 8 * m + 1241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6187.1, data_15_6187.2]

/-- Complete interval computation for depth 15, residue 6188. -/
theorem bounds_15_6188 : exactInterval 15 6188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6188 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6188) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6188 : oddCount 6188 15 = 5 ∧ acceleratedOrbit 15 6188 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6188 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6188) = 3 ^ 5 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6188.1, data_15_6188.2]

/-- Complete interval computation for depth 15, residue 6189. -/
theorem bounds_15_6189 : exactInterval 15 6189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6189 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6189) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6189 : oddCount 6189 15 = 5 ∧ acceleratedOrbit 15 6189 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6189 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6189) = 3 ^ 5 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6189.1, data_15_6189.2]

/-- Complete interval computation for depth 15, residue 6190. -/
theorem bounds_15_6190 : exactInterval 15 6190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6190 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6190) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6190 : oddCount 6190 15 = 5 ∧ acceleratedOrbit 15 6190 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6190 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6190) = 3 ^ 5 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6190.1, data_15_6190.2]

/-- Complete interval computation for depth 15, residue 6191. -/
theorem bounds_15_6191 : exactInterval 15 6191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6191 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6191) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6191 : oddCount 6191 15 = 11 ∧ acceleratedOrbit 15 6191 = 33479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6191 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6191) = 3 ^ 11 * m + 33479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6191.1, data_15_6191.2]

/-- Complete interval computation for depth 15, residue 6192. -/
theorem bounds_15_6192 : exactInterval 15 6192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6192 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6192) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6192 : oddCount 6192 15 = 5 ∧ acceleratedOrbit 15 6192 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6192 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6192) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6192.1, data_15_6192.2]

end Collatz.Research.PassageAtlas.Batch0189
