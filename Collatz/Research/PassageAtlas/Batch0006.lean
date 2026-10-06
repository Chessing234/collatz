import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0006

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 163. -/
theorem bounds_15_163 : exactInterval 15 163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_163 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 163) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_163 : oddCount 163 15 = 6 ∧ acceleratedOrbit 15 163 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_163 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 163) = 3 ^ 6 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_163.1, data_15_163.2]

/-- Complete interval computation for depth 15, residue 164. -/
theorem bounds_15_164 : exactInterval 15 164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_164 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 164) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_164 : oddCount 164 15 = 9 ∧ acceleratedOrbit 15 164 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_164 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 164) = 3 ^ 9 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_164.1, data_15_164.2]

/-- Complete interval computation for depth 15, residue 165. -/
theorem bounds_15_165 : exactInterval 15 165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_165 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 165) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_165 : oddCount 165 15 = 9 ∧ acceleratedOrbit 15 165 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_165 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 165) = 3 ^ 9 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_165.1, data_15_165.2]

/-- Complete interval computation for depth 15, residue 166. -/
theorem bounds_15_166 : exactInterval 15 166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_166 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 166) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_166 : oddCount 166 15 = 9 ∧ acceleratedOrbit 15 166 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_166 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 166) = 3 ^ 9 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_166.1, data_15_166.2]

/-- Complete interval computation for depth 15, residue 167. -/
theorem bounds_15_167 : exactInterval 15 167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_167 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 167) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_167 : oddCount 167 15 = 11 ∧ acceleratedOrbit 15 167 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_167 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 167) = 3 ^ 11 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_167.1, data_15_167.2]

/-- Complete interval computation for depth 15, residue 168. -/
theorem bounds_15_168 : exactInterval 15 168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_168 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 168) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_168 : oddCount 168 15 = 4 ∧ acceleratedOrbit 15 168 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_168 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 168) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_168.1, data_15_168.2]

/-- Complete interval computation for depth 15, residue 169. -/
theorem bounds_15_169 : exactInterval 15 169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_169 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 169) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_169 : oddCount 169 15 = 10 ∧ acceleratedOrbit 15 169 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_169 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 169) = 3 ^ 10 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_169.1, data_15_169.2]

/-- Complete interval computation for depth 15, residue 170. -/
theorem bounds_15_170 : exactInterval 15 170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_170 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 170) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_170 : oddCount 170 15 = 4 ∧ acceleratedOrbit 15 170 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_170 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 170) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_170.1, data_15_170.2]

/-- Complete interval computation for depth 15, residue 171. -/
theorem bounds_15_171 : exactInterval 15 171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_171 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 171) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_171 : oddCount 171 15 = 9 ∧ acceleratedOrbit 15 171 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_171 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 171) = 3 ^ 9 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_171.1, data_15_171.2]

/-- Complete interval computation for depth 15, residue 172. -/
theorem bounds_15_172 : exactInterval 15 172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_172 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 172) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_172 : oddCount 172 15 = 7 ∧ acceleratedOrbit 15 172 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_172 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 172) = 3 ^ 7 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_172.1, data_15_172.2]

/-- Complete interval computation for depth 15, residue 173. -/
theorem bounds_15_173 : exactInterval 15 173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_173 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 173) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_173 : oddCount 173 15 = 7 ∧ acceleratedOrbit 15 173 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_173 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 173) = 3 ^ 7 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_173.1, data_15_173.2]

/-- Complete interval computation for depth 15, residue 174. -/
theorem bounds_15_174 : exactInterval 15 174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_174 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 174) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_174 : oddCount 174 15 = 7 ∧ acceleratedOrbit 15 174 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_174 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 174) = 3 ^ 7 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_174.1, data_15_174.2]

/-- Complete interval computation for depth 15, residue 175. -/
theorem bounds_15_175 : exactInterval 15 175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_175 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 175) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_175 : oddCount 175 15 = 10 ∧ acceleratedOrbit 15 175 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_175 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 175) = 3 ^ 10 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_175.1, data_15_175.2]

/-- Complete interval computation for depth 15, residue 176. -/
theorem bounds_15_176 : exactInterval 15 176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_176 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 176) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_176 : oddCount 176 15 = 5 ∧ acceleratedOrbit 15 176 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_176 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 176) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_176.1, data_15_176.2]

/-- Complete interval computation for depth 15, residue 177. -/
theorem bounds_15_177 : exactInterval 15 177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_177 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 177) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_177 : oddCount 177 15 = 7 ∧ acceleratedOrbit 15 177 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_177 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 177) = 3 ^ 7 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_177.1, data_15_177.2]

/-- Complete interval computation for depth 15, residue 178. -/
theorem bounds_15_178 : exactInterval 15 178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_178 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 178) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_178 : oddCount 178 15 = 7 ∧ acceleratedOrbit 15 178 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_178 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 178) = 3 ^ 7 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_178.1, data_15_178.2]

/-- Complete interval computation for depth 15, residue 179. -/
theorem bounds_15_179 : exactInterval 15 179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_179 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 179) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_179 : oddCount 179 15 = 7 ∧ acceleratedOrbit 15 179 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_179 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 179) = 3 ^ 7 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_179.1, data_15_179.2]

/-- Complete interval computation for depth 15, residue 180. -/
theorem bounds_15_180 : exactInterval 15 180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_180 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 180) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_180 : oddCount 180 15 = 5 ∧ acceleratedOrbit 15 180 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_180 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 180) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_180.1, data_15_180.2]

/-- Complete interval computation for depth 15, residue 181. -/
theorem bounds_15_181 : exactInterval 15 181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_181 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 181) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_181 : oddCount 181 15 = 5 ∧ acceleratedOrbit 15 181 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_181 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 181) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_181.1, data_15_181.2]

/-- Complete interval computation for depth 15, residue 182. -/
theorem bounds_15_182 : exactInterval 15 182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_182 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 182) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_182 : oddCount 182 15 = 10 ∧ acceleratedOrbit 15 182 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_182 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 182) = 3 ^ 10 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_182.1, data_15_182.2]

/-- Complete interval computation for depth 15, residue 183. -/
theorem bounds_15_183 : exactInterval 15 183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_183 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 183) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_183 : oddCount 183 15 = 10 ∧ acceleratedOrbit 15 183 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_183 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 183) = 3 ^ 10 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_183.1, data_15_183.2]

/-- Complete interval computation for depth 15, residue 184. -/
theorem bounds_15_184 : exactInterval 15 184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_184 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 184) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_184 : oddCount 184 15 = 5 ∧ acceleratedOrbit 15 184 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_184 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 184) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_184.1, data_15_184.2]

/-- Complete interval computation for depth 15, residue 185. -/
theorem bounds_15_185 : exactInterval 15 185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_185 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 185) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_185 : oddCount 185 15 = 8 ∧ acceleratedOrbit 15 185 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_185 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 185) = 3 ^ 8 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_185.1, data_15_185.2]

/-- Complete interval computation for depth 15, residue 186. -/
theorem bounds_15_186 : exactInterval 15 186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_186 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 186) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_186 : oddCount 186 15 = 5 ∧ acceleratedOrbit 15 186 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_186 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 186) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_186.1, data_15_186.2]

/-- Complete interval computation for depth 15, residue 187. -/
theorem bounds_15_187 : exactInterval 15 187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_187 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 187) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_187 : oddCount 187 15 = 8 ∧ acceleratedOrbit 15 187 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_187 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 187) = 3 ^ 8 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_187.1, data_15_187.2]

/-- Complete interval computation for depth 15, residue 188. -/
theorem bounds_15_188 : exactInterval 15 188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_188 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 188) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_188 : oddCount 188 15 = 10 ∧ acceleratedOrbit 15 188 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_188 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 188) = 3 ^ 10 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_188.1, data_15_188.2]

/-- Complete interval computation for depth 15, residue 189. -/
theorem bounds_15_189 : exactInterval 15 189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_189 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 189) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_189 : oddCount 189 15 = 10 ∧ acceleratedOrbit 15 189 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_189 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 189) = 3 ^ 10 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_189.1, data_15_189.2]

/-- Complete interval computation for depth 15, residue 190. -/
theorem bounds_15_190 : exactInterval 15 190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_190 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 190) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_190 : oddCount 190 15 = 10 ∧ acceleratedOrbit 15 190 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_190 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 190) = 3 ^ 10 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_190.1, data_15_190.2]

/-- Complete interval computation for depth 15, residue 191. -/
theorem bounds_15_191 : exactInterval 15 191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_191 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 191) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_191 : oddCount 191 15 = 9 ∧ acceleratedOrbit 15 191 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_191 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 191) = 3 ^ 9 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_191.1, data_15_191.2]

/-- Complete interval computation for depth 15, residue 192. -/
theorem bounds_15_192 : exactInterval 15 192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_192 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 192) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_192 : oddCount 192 15 = 4 ∧ acceleratedOrbit 15 192 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_192 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 192) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_192.1, data_15_192.2]

/-- Complete interval computation for depth 15, residue 193. -/
theorem bounds_15_193 : exactInterval 15 193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_193 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 193) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_193 : oddCount 193 15 = 9 ∧ acceleratedOrbit 15 193 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_193 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 193) = 3 ^ 9 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_193.1, data_15_193.2]

/-- Complete interval computation for depth 15, residue 194. -/
theorem bounds_15_194 : exactInterval 15 194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_194 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 194) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_194 : oddCount 194 15 = 9 ∧ acceleratedOrbit 15 194 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_194 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 194) = 3 ^ 9 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_194.1, data_15_194.2]

/-- Complete interval computation for depth 15, residue 195. -/
theorem bounds_15_195 : exactInterval 15 195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_195 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 195) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_195 : oddCount 195 15 = 9 ∧ acceleratedOrbit 15 195 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_195 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 195) = 3 ^ 9 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_195.1, data_15_195.2]

end Collatz.Research.PassageAtlas.Batch0006
