import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0481

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 204. -/
theorem bounds_13_204 : exactInterval 13 204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_204 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 204) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_204 : oddCount 204 13 = 6 ∧ acceleratedOrbit 13 204 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_204 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 204) = 3 ^ 6 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_204.1, data_13_204.2]

/-- Complete interval computation for depth 13, residue 205. -/
theorem bounds_13_205 : exactInterval 13 205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_205 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 205) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_205 : oddCount 205 13 = 6 ∧ acceleratedOrbit 13 205 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_205 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 205) = 3 ^ 6 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_205.1, data_13_205.2]

/-- Complete interval computation for depth 13, residue 206. -/
theorem bounds_13_206 : exactInterval 13 206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_206 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 206) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_206 : oddCount 206 13 = 8 ∧ acceleratedOrbit 13 206 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_206 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 206) = 3 ^ 8 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_206.1, data_13_206.2]

/-- Complete interval computation for depth 13, residue 207. -/
theorem bounds_13_207 : exactInterval 13 207 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_207 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 207) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_207 : oddCount 207 13 = 8 ∧ acceleratedOrbit 13 207 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_207 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 207) = 3 ^ 8 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_207.1, data_13_207.2]

/-- Complete interval computation for depth 13, residue 208. -/
theorem bounds_13_208 : exactInterval 13 208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_208 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 208) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_208 : oddCount 208 13 = 3 ∧ acceleratedOrbit 13 208 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_208 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 208) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_208.1, data_13_208.2]

/-- Complete interval computation for depth 13, residue 209. -/
theorem bounds_13_209 : exactInterval 13 209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_209 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 209) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_209 : oddCount 209 13 = 6 ∧ acceleratedOrbit 13 209 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_209 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 209) = 3 ^ 6 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_209.1, data_13_209.2]

/-- Complete interval computation for depth 13, residue 210. -/
theorem bounds_13_210 : exactInterval 13 210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_210 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 210) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_210 : oddCount 210 13 = 6 ∧ acceleratedOrbit 13 210 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_210 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 210) = 3 ^ 6 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_210.1, data_13_210.2]

/-- Complete interval computation for depth 13, residue 211. -/
theorem bounds_13_211 : exactInterval 13 211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_211 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 211) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_211 : oddCount 211 13 = 6 ∧ acceleratedOrbit 13 211 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_211 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 211) = 3 ^ 6 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_211.1, data_13_211.2]

/-- Complete interval computation for depth 13, residue 212. -/
theorem bounds_13_212 : exactInterval 13 212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_212 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 212) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_212 : oddCount 212 13 = 3 ∧ acceleratedOrbit 13 212 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_212 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 212) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_212.1, data_13_212.2]

/-- Complete interval computation for depth 13, residue 213. -/
theorem bounds_13_213 : exactInterval 13 213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_213 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 213) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_213 : oddCount 213 13 = 3 ∧ acceleratedOrbit 13 213 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_213 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 213) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_213.1, data_13_213.2]

/-- Complete interval computation for depth 13, residue 214. -/
theorem bounds_13_214 : exactInterval 13 214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_214 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 214) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_214 : oddCount 214 13 = 8 ∧ acceleratedOrbit 13 214 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_214 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 214) = 3 ^ 8 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_214.1, data_13_214.2]

/-- Complete interval computation for depth 13, residue 215. -/
theorem bounds_13_215 : exactInterval 13 215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_215 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 215) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_215 : oddCount 215 13 = 8 ∧ acceleratedOrbit 13 215 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_215 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 215) = 3 ^ 8 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_215.1, data_13_215.2]

/-- Complete interval computation for depth 13, residue 216. -/
theorem bounds_13_216 : exactInterval 13 216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_216 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 216) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_216 : oddCount 216 13 = 8 ∧ acceleratedOrbit 13 216 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_216 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 216) = 3 ^ 8 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_216.1, data_13_216.2]

/-- Complete interval computation for depth 13, residue 217. -/
theorem bounds_13_217 : exactInterval 13 217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_217 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 217) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_217 : oddCount 217 13 = 6 ∧ acceleratedOrbit 13 217 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_217 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 217) = 3 ^ 6 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_217.1, data_13_217.2]

/-- Complete interval computation for depth 13, residue 218. -/
theorem bounds_13_218 : exactInterval 13 218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_218 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 218) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_218 : oddCount 218 13 = 8 ∧ acceleratedOrbit 13 218 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_218 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 218) = 3 ^ 8 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_218.1, data_13_218.2]

/-- Complete interval computation for depth 13, residue 219. -/
theorem bounds_13_219 : exactInterval 13 219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_219 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 219) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_219 : oddCount 219 13 = 7 ∧ acceleratedOrbit 13 219 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_219 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 219) = 3 ^ 7 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_219.1, data_13_219.2]

end Collatz.Research.StoppingAtlas.Batch0481
