import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0215

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 215. -/
theorem bounds_12_215 : exactInterval 12 215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_215 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 215) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_215 : oddCount 215 12 = 8 ∧ acceleratedOrbit 12 215 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_215 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 215) = 3 ^ 8 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_215.1, data_12_215.2]

/-- Complete interval computation for depth 12, residue 216. -/
theorem bounds_12_216 : exactInterval 12 216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_216 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 216) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_216 : oddCount 216 12 = 7 ∧ acceleratedOrbit 12 216 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_216 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 216) = 3 ^ 7 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_216.1, data_12_216.2]

/-- Complete interval computation for depth 12, residue 217. -/
theorem bounds_12_217 : exactInterval 12 217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_217 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 217) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_217 : oddCount 217 12 = 6 ∧ acceleratedOrbit 12 217 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_217 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 217) = 3 ^ 6 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_217.1, data_12_217.2]

/-- Complete interval computation for depth 12, residue 218. -/
theorem bounds_12_218 : exactInterval 12 218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_218 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 218) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_218 : oddCount 218 12 = 7 ∧ acceleratedOrbit 12 218 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_218 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 218) = 3 ^ 7 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_218.1, data_12_218.2]

/-- Complete interval computation for depth 12, residue 219. -/
theorem bounds_12_219 : exactInterval 12 219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_219 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 219) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_219 : oddCount 219 12 = 7 ∧ acceleratedOrbit 12 219 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_219 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 219) = 3 ^ 7 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_219.1, data_12_219.2]

/-- Complete interval computation for depth 12, residue 220. -/
theorem bounds_12_220 : exactInterval 12 220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_220 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 220) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_220 : oddCount 220 12 = 7 ∧ acceleratedOrbit 12 220 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_220 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 220) = 3 ^ 7 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_220.1, data_12_220.2]

/-- Complete interval computation for depth 12, residue 221. -/
theorem bounds_12_221 : exactInterval 12 221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_221 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 221) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_221 : oddCount 221 12 = 7 ∧ acceleratedOrbit 12 221 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_221 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 221) = 3 ^ 7 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_221.1, data_12_221.2]

/-- Complete interval computation for depth 12, residue 222. -/
theorem bounds_12_222 : exactInterval 12 222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_222 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 222) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_222 : oddCount 222 12 = 9 ∧ acceleratedOrbit 12 222 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_222 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 222) = 3 ^ 9 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_222.1, data_12_222.2]

/-- Complete interval computation for depth 12, residue 223. -/
theorem bounds_12_223 : exactInterval 12 223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_223 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 223) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_223 : oddCount 223 12 = 9 ∧ acceleratedOrbit 12 223 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_223 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 223) = 3 ^ 9 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_223.1, data_12_223.2]

/-- Complete interval computation for depth 12, residue 224. -/
theorem bounds_12_224 : exactInterval 12 224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_224 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 224) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_224 : oddCount 224 12 = 4 ∧ acceleratedOrbit 12 224 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_224 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 224) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_224.1, data_12_224.2]

/-- Complete interval computation for depth 12, residue 225. -/
theorem bounds_12_225 : exactInterval 12 225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_225 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 225) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_225 : oddCount 225 12 = 9 ∧ acceleratedOrbit 12 225 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_225 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 225) = 3 ^ 9 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_225.1, data_12_225.2]

/-- Complete interval computation for depth 12, residue 226. -/
theorem bounds_12_226 : exactInterval 12 226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_226 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 226) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_226 : oddCount 226 12 = 3 ∧ acceleratedOrbit 12 226 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_226 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 226) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_226.1, data_12_226.2]

/-- Complete interval computation for depth 12, residue 227. -/
theorem bounds_12_227 : exactInterval 12 227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_227 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 227) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_227 : oddCount 227 12 = 3 ∧ acceleratedOrbit 12 227 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_227 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 227) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_227.1, data_12_227.2]

/-- Complete interval computation for depth 12, residue 228. -/
theorem bounds_12_228 : exactInterval 12 228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_228 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 228) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_228 : oddCount 228 12 = 5 ∧ acceleratedOrbit 12 228 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_228 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 228) = 3 ^ 5 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_228.1, data_12_228.2]

/-- Complete interval computation for depth 12, residue 229. -/
theorem bounds_12_229 : exactInterval 12 229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_229 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 229) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_229 : oddCount 229 12 = 5 ∧ acceleratedOrbit 12 229 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_229 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 229) = 3 ^ 5 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_229.1, data_12_229.2]

end Collatz.Research.StoppingAtlas.Batch0215
