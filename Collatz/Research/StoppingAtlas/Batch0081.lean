import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0081

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 204. -/
theorem bounds_11_204 : exactInterval 11 204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_204 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 204) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_204 : oddCount 204 11 = 5 ∧ acceleratedOrbit 11 204 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_204 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 204) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_204.1, data_11_204.2]

/-- Complete interval computation for depth 11, residue 205. -/
theorem bounds_11_205 : exactInterval 11 205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_205 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 205) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_205 : oddCount 205 11 = 5 ∧ acceleratedOrbit 11 205 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_205 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 205) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_205.1, data_11_205.2]

/-- Complete interval computation for depth 11, residue 206. -/
theorem bounds_11_206 : exactInterval 11 206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_206 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 206) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_206 : oddCount 206 11 = 8 ∧ acceleratedOrbit 11 206 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_206 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 206) = 3 ^ 8 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_206.1, data_11_206.2]

/-- Complete interval computation for depth 11, residue 207. -/
theorem bounds_11_207 : exactInterval 11 207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_207 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 207) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_207 : oddCount 207 11 = 8 ∧ acceleratedOrbit 11 207 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_207 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 207) = 3 ^ 8 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_207.1, data_11_207.2]

/-- Complete interval computation for depth 11, residue 208. -/
theorem bounds_11_208 : exactInterval 11 208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_208 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 208) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_208 : oddCount 208 11 = 2 ∧ acceleratedOrbit 11 208 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_208 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 208) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_208.1, data_11_208.2]

/-- Complete interval computation for depth 11, residue 209. -/
theorem bounds_11_209 : exactInterval 11 209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_209 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 209) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_209 : oddCount 209 11 = 6 ∧ acceleratedOrbit 11 209 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_209 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 209) = 3 ^ 6 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_209.1, data_11_209.2]

/-- Complete interval computation for depth 11, residue 210. -/
theorem bounds_11_210 : exactInterval 11 210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_210 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 210) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_210 : oddCount 210 11 = 6 ∧ acceleratedOrbit 11 210 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_210 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 210) = 3 ^ 6 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_210.1, data_11_210.2]

/-- Complete interval computation for depth 11, residue 211. -/
theorem bounds_11_211 : exactInterval 11 211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_211 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 211) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_211 : oddCount 211 11 = 6 ∧ acceleratedOrbit 11 211 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_211 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 211) = 3 ^ 6 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_211.1, data_11_211.2]

/-- Complete interval computation for depth 11, residue 212. -/
theorem bounds_11_212 : exactInterval 11 212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_212 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 212) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_212 : oddCount 212 11 = 2 ∧ acceleratedOrbit 11 212 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_212 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 212) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_212.1, data_11_212.2]

/-- Complete interval computation for depth 11, residue 213. -/
theorem bounds_11_213 : exactInterval 11 213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_213 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 213) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_213 : oddCount 213 11 = 2 ∧ acceleratedOrbit 11 213 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_213 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 213) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_213.1, data_11_213.2]

/-- Complete interval computation for depth 11, residue 214. -/
theorem bounds_11_214 : exactInterval 11 214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_214 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 214) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_214 : oddCount 214 11 = 7 ∧ acceleratedOrbit 11 214 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_214 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 214) = 3 ^ 7 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_214.1, data_11_214.2]

/-- Complete interval computation for depth 11, residue 215. -/
theorem bounds_11_215 : exactInterval 11 215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_215 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 215) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_215 : oddCount 215 11 = 7 ∧ acceleratedOrbit 11 215 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_215 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 215) = 3 ^ 7 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_215.1, data_11_215.2]

/-- Complete interval computation for depth 11, residue 216. -/
theorem bounds_11_216 : exactInterval 11 216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_216 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 216) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_216 : oddCount 216 11 = 7 ∧ acceleratedOrbit 11 216 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_216 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 216) = 3 ^ 7 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_216.1, data_11_216.2]

/-- Complete interval computation for depth 11, residue 217. -/
theorem bounds_11_217 : exactInterval 11 217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_217 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 217) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_217 : oddCount 217 11 = 6 ∧ acceleratedOrbit 11 217 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_217 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 217) = 3 ^ 6 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_217.1, data_11_217.2]

/-- Complete interval computation for depth 11, residue 218. -/
theorem bounds_11_218 : exactInterval 11 218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_218 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 218) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_218 : oddCount 218 11 = 7 ∧ acceleratedOrbit 11 218 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_218 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 218) = 3 ^ 7 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_218.1, data_11_218.2]

/-- Complete interval computation for depth 11, residue 219. -/
theorem bounds_11_219 : exactInterval 11 219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_219 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 219) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_219 : oddCount 219 11 = 7 ∧ acceleratedOrbit 11 219 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_219 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 219) = 3 ^ 7 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_219.1, data_11_219.2]

end Collatz.Research.StoppingAtlas.Batch0081
