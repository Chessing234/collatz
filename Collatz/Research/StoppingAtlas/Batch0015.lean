import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0015

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 215. -/
theorem bounds_10_215 : exactInterval 10 215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_215 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 215) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_215 : oddCount 215 10 = 6 ∧ acceleratedOrbit 10 215 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_215 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 215) = 3 ^ 6 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_215.1, data_10_215.2]

/-- Complete interval computation for depth 10, residue 216. -/
theorem bounds_10_216 : exactInterval 10 216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_216 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 216) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_216 : oddCount 216 10 = 6 ∧ acceleratedOrbit 10 216 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_216 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 216) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_216.1, data_10_216.2]

/-- Complete interval computation for depth 10, residue 217. -/
theorem bounds_10_217 : exactInterval 10 217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_217 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 217) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_217 : oddCount 217 10 = 5 ∧ acceleratedOrbit 10 217 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_217 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 217) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_217.1, data_10_217.2]

/-- Complete interval computation for depth 10, residue 218. -/
theorem bounds_10_218 : exactInterval 10 218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_218 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 218) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_218 : oddCount 218 10 = 6 ∧ acceleratedOrbit 10 218 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_218 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 218) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_218.1, data_10_218.2]

/-- Complete interval computation for depth 10, residue 219. -/
theorem bounds_10_219 : exactInterval 10 219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_219 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 219) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_219 : oddCount 219 10 = 6 ∧ acceleratedOrbit 10 219 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_219 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 219) = 3 ^ 6 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_219.1, data_10_219.2]

/-- Complete interval computation for depth 10, residue 220. -/
theorem bounds_10_220 : exactInterval 10 220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_220 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 220) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_220 : oddCount 220 10 = 6 ∧ acceleratedOrbit 10 220 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_220 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 220) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_220.1, data_10_220.2]

/-- Complete interval computation for depth 10, residue 221. -/
theorem bounds_10_221 : exactInterval 10 221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_221 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 221) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_221 : oddCount 221 10 = 6 ∧ acceleratedOrbit 10 221 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_221 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 221) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_221.1, data_10_221.2]

/-- Complete interval computation for depth 10, residue 222. -/
theorem bounds_10_222 : exactInterval 10 222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_222 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 222) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_222 : oddCount 222 10 = 7 ∧ acceleratedOrbit 10 222 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_222 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 222) = 3 ^ 7 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_222.1, data_10_222.2]

/-- Complete interval computation for depth 10, residue 223. -/
theorem bounds_10_223 : exactInterval 10 223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_223 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 223) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_223 : oddCount 223 10 = 7 ∧ acceleratedOrbit 10 223 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_223 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 223) = 3 ^ 7 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_223.1, data_10_223.2]

/-- Complete interval computation for depth 10, residue 224. -/
theorem bounds_10_224 : exactInterval 10 224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_224 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 224) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_224 : oddCount 224 10 = 4 ∧ acceleratedOrbit 10 224 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_224 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 224) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_224.1, data_10_224.2]

/-- Complete interval computation for depth 10, residue 225. -/
theorem bounds_10_225 : exactInterval 10 225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_225 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 225) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_225 : oddCount 225 10 = 8 ∧ acceleratedOrbit 10 225 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_225 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 225) = 3 ^ 8 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_225.1, data_10_225.2]

/-- Complete interval computation for depth 10, residue 226. -/
theorem bounds_10_226 : exactInterval 10 226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_226 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 226) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_226 : oddCount 226 10 = 2 ∧ acceleratedOrbit 10 226 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_226 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 226) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_226.1, data_10_226.2]

/-- Complete interval computation for depth 10, residue 227. -/
theorem bounds_10_227 : exactInterval 10 227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_227 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 227) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_227 : oddCount 227 10 = 2 ∧ acceleratedOrbit 10 227 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_227 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 227) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_227.1, data_10_227.2]

/-- Complete interval computation for depth 10, residue 228. -/
theorem bounds_10_228 : exactInterval 10 228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_228 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 228) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_228 : oddCount 228 10 = 5 ∧ acceleratedOrbit 10 228 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_228 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 228) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_228.1, data_10_228.2]

/-- Complete interval computation for depth 10, residue 229. -/
theorem bounds_10_229 : exactInterval 10 229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_229 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 229) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_229 : oddCount 229 10 = 5 ∧ acceleratedOrbit 10 229 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_229 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 229) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_229.1, data_10_229.2]

end Collatz.Research.StoppingAtlas.Batch0015
