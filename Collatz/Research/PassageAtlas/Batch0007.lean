import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0007

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 196. -/
theorem bounds_15_196 : exactInterval 15 196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_196 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 196) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_196 : oddCount 196 15 = 6 ∧ acceleratedOrbit 15 196 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_196 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 196) = 3 ^ 6 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_196.1, data_15_196.2]

/-- Complete interval computation for depth 15, residue 197. -/
theorem bounds_15_197 : exactInterval 15 197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_197 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 197) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_197 : oddCount 197 15 = 6 ∧ acceleratedOrbit 15 197 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_197 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 197) = 3 ^ 6 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_197.1, data_15_197.2]

/-- Complete interval computation for depth 15, residue 198. -/
theorem bounds_15_198 : exactInterval 15 198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_198 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 198) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_198 : oddCount 198 15 = 6 ∧ acceleratedOrbit 15 198 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_198 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 198) = 3 ^ 6 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_198.1, data_15_198.2]

/-- Complete interval computation for depth 15, residue 199. -/
theorem bounds_15_199 : exactInterval 15 199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_199 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 199) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_199 : oddCount 199 15 = 10 ∧ acceleratedOrbit 15 199 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_199 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 199) = 3 ^ 10 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_199.1, data_15_199.2]

/-- Complete interval computation for depth 15, residue 200. -/
theorem bounds_15_200 : exactInterval 15 200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_200 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 200) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_200 : oddCount 200 15 = 6 ∧ acceleratedOrbit 15 200 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_200 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 200) = 3 ^ 6 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_200.1, data_15_200.2]

/-- Complete interval computation for depth 15, residue 201. -/
theorem bounds_15_201 : exactInterval 15 201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_201 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 201) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_201 : oddCount 201 15 = 5 ∧ acceleratedOrbit 15 201 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_201 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 201) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_201.1, data_15_201.2]

/-- Complete interval computation for depth 15, residue 202. -/
theorem bounds_15_202 : exactInterval 15 202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_202 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 202) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_202 : oddCount 202 15 = 6 ∧ acceleratedOrbit 15 202 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_202 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 202) = 3 ^ 6 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_202.1, data_15_202.2]

/-- Complete interval computation for depth 15, residue 203. -/
theorem bounds_15_203 : exactInterval 15 203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_203 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 203) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_203 : oddCount 203 15 = 7 ∧ acceleratedOrbit 15 203 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_203 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 203) = 3 ^ 7 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_203.1, data_15_203.2]

/-- Complete interval computation for depth 15, residue 204. -/
theorem bounds_15_204 : exactInterval 15 204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_204 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 204) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_204 : oddCount 204 15 = 6 ∧ acceleratedOrbit 15 204 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_204 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 204) = 3 ^ 6 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_204.1, data_15_204.2]

/-- Complete interval computation for depth 15, residue 205. -/
theorem bounds_15_205 : exactInterval 15 205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_205 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 205) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_205 : oddCount 205 15 = 6 ∧ acceleratedOrbit 15 205 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_205 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 205) = 3 ^ 6 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_205.1, data_15_205.2]

/-- Complete interval computation for depth 15, residue 206. -/
theorem bounds_15_206 : exactInterval 15 206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_206 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 206) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_206 : oddCount 206 15 = 10 ∧ acceleratedOrbit 15 206 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_206 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 206) = 3 ^ 10 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_206.1, data_15_206.2]

/-- Complete interval computation for depth 15, residue 207. -/
theorem bounds_15_207 : exactInterval 15 207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_207 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 207) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_207 : oddCount 207 15 = 10 ∧ acceleratedOrbit 15 207 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_207 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 207) = 3 ^ 10 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_207.1, data_15_207.2]

/-- Complete interval computation for depth 15, residue 208. -/
theorem bounds_15_208 : exactInterval 15 208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_208 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 208) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_208 : oddCount 208 15 = 4 ∧ acceleratedOrbit 15 208 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_208 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 208) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_208.1, data_15_208.2]

/-- Complete interval computation for depth 15, residue 209. -/
theorem bounds_15_209 : exactInterval 15 209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_209 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 209) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_209 : oddCount 209 15 = 8 ∧ acceleratedOrbit 15 209 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_209 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 209) = 3 ^ 8 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_209.1, data_15_209.2]

/-- Complete interval computation for depth 15, residue 210. -/
theorem bounds_15_210 : exactInterval 15 210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_210 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 210) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_210 : oddCount 210 15 = 8 ∧ acceleratedOrbit 15 210 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_210 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 210) = 3 ^ 8 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_210.1, data_15_210.2]

/-- Complete interval computation for depth 15, residue 211. -/
theorem bounds_15_211 : exactInterval 15 211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_211 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 211) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_211 : oddCount 211 15 = 8 ∧ acceleratedOrbit 15 211 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_211 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 211) = 3 ^ 8 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_211.1, data_15_211.2]

/-- Complete interval computation for depth 15, residue 212. -/
theorem bounds_15_212 : exactInterval 15 212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_212 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 212) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_212 : oddCount 212 15 = 4 ∧ acceleratedOrbit 15 212 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_212 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 212) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_212.1, data_15_212.2]

/-- Complete interval computation for depth 15, residue 213. -/
theorem bounds_15_213 : exactInterval 15 213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_213 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 213) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_213 : oddCount 213 15 = 4 ∧ acceleratedOrbit 15 213 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_213 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 213) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_213.1, data_15_213.2]

/-- Complete interval computation for depth 15, residue 214. -/
theorem bounds_15_214 : exactInterval 15 214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_214 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 214) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_214 : oddCount 214 15 = 10 ∧ acceleratedOrbit 15 214 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_214 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 214) = 3 ^ 10 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_214.1, data_15_214.2]

/-- Complete interval computation for depth 15, residue 215. -/
theorem bounds_15_215 : exactInterval 15 215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_215 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 215) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_215 : oddCount 215 15 = 10 ∧ acceleratedOrbit 15 215 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_215 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 215) = 3 ^ 10 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_215.1, data_15_215.2]

/-- Complete interval computation for depth 15, residue 216. -/
theorem bounds_15_216 : exactInterval 15 216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_216 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 216) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_216 : oddCount 216 15 = 9 ∧ acceleratedOrbit 15 216 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_216 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 216) = 3 ^ 9 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_216.1, data_15_216.2]

/-- Complete interval computation for depth 15, residue 217. -/
theorem bounds_15_217 : exactInterval 15 217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_217 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 217) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_217 : oddCount 217 15 = 6 ∧ acceleratedOrbit 15 217 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_217 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 217) = 3 ^ 6 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_217.1, data_15_217.2]

/-- Complete interval computation for depth 15, residue 218. -/
theorem bounds_15_218 : exactInterval 15 218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_218 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 218) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_218 : oddCount 218 15 = 9 ∧ acceleratedOrbit 15 218 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_218 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 218) = 3 ^ 9 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_218.1, data_15_218.2]

/-- Complete interval computation for depth 15, residue 219. -/
theorem bounds_15_219 : exactInterval 15 219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_219 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 219) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_219 : oddCount 219 15 = 9 ∧ acceleratedOrbit 15 219 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_219 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 219) = 3 ^ 9 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_219.1, data_15_219.2]

/-- Complete interval computation for depth 15, residue 220. -/
theorem bounds_15_220 : exactInterval 15 220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_220 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 220) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_220 : oddCount 220 15 = 9 ∧ acceleratedOrbit 15 220 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_220 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 220) = 3 ^ 9 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_220.1, data_15_220.2]

/-- Complete interval computation for depth 15, residue 221. -/
theorem bounds_15_221 : exactInterval 15 221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_221 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 221) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_221 : oddCount 221 15 = 9 ∧ acceleratedOrbit 15 221 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_221 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 221) = 3 ^ 9 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_221.1, data_15_221.2]

/-- Complete interval computation for depth 15, residue 222. -/
theorem bounds_15_222 : exactInterval 15 222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_222 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 222) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_222 : oddCount 222 15 = 12 ∧ acceleratedOrbit 15 222 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_222 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 222) = 3 ^ 12 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_222.1, data_15_222.2]

/-- Complete interval computation for depth 15, residue 223. -/
theorem bounds_15_223 : exactInterval 15 223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_223 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 223) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_223 : oddCount 223 15 = 12 ∧ acceleratedOrbit 15 223 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_223 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 223) = 3 ^ 12 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_223.1, data_15_223.2]

/-- Complete interval computation for depth 15, residue 224. -/
theorem bounds_15_224 : exactInterval 15 224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_224 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 224) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_224 : oddCount 224 15 = 5 ∧ acceleratedOrbit 15 224 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_224 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 224) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_224.1, data_15_224.2]

/-- Complete interval computation for depth 15, residue 225. -/
theorem bounds_15_225 : exactInterval 15 225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_225 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 225) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_225 : oddCount 225 15 = 10 ∧ acceleratedOrbit 15 225 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_225 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 225) = 3 ^ 10 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_225.1, data_15_225.2]

/-- Complete interval computation for depth 15, residue 226. -/
theorem bounds_15_226 : exactInterval 15 226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_226 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 226) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_226 : oddCount 226 15 = 4 ∧ acceleratedOrbit 15 226 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_226 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 226) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_226.1, data_15_226.2]

/-- Complete interval computation for depth 15, residue 227. -/
theorem bounds_15_227 : exactInterval 15 227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_227 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 227) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_227 : oddCount 227 15 = 4 ∧ acceleratedOrbit 15 227 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_227 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 227) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_227.1, data_15_227.2]

/-- Complete interval computation for depth 15, residue 228. -/
theorem bounds_15_228 : exactInterval 15 228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_228 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 228) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_228 : oddCount 228 15 = 7 ∧ acceleratedOrbit 15 228 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_228 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 228) = 3 ^ 7 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_228.1, data_15_228.2]

end Collatz.Research.PassageAtlas.Batch0007
