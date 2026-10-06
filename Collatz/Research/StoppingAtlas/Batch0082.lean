import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0082

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 220. -/
theorem bounds_11_220 : exactInterval 11 220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_220 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 220) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_220 : oddCount 220 11 = 7 ∧ acceleratedOrbit 11 220 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_220 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 220) = 3 ^ 7 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_220.1, data_11_220.2]

/-- Complete interval computation for depth 11, residue 221. -/
theorem bounds_11_221 : exactInterval 11 221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_221 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 221) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_221 : oddCount 221 11 = 7 ∧ acceleratedOrbit 11 221 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_221 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 221) = 3 ^ 7 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_221.1, data_11_221.2]

/-- Complete interval computation for depth 11, residue 222. -/
theorem bounds_11_222 : exactInterval 11 222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_222 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 222) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_222 : oddCount 222 11 = 8 ∧ acceleratedOrbit 11 222 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_222 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 222) = 3 ^ 8 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_222.1, data_11_222.2]

/-- Complete interval computation for depth 11, residue 223. -/
theorem bounds_11_223 : exactInterval 11 223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_223 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 223) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_223 : oddCount 223 11 = 8 ∧ acceleratedOrbit 11 223 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_223 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 223) = 3 ^ 8 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_223.1, data_11_223.2]

/-- Complete interval computation for depth 11, residue 224. -/
theorem bounds_11_224 : exactInterval 11 224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_224 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 224) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_224 : oddCount 224 11 = 4 ∧ acceleratedOrbit 11 224 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_224 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 224) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_224.1, data_11_224.2]

/-- Complete interval computation for depth 11, residue 225. -/
theorem bounds_11_225 : exactInterval 11 225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_225 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 225) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_225 : oddCount 225 11 = 9 ∧ acceleratedOrbit 11 225 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_225 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 225) = 3 ^ 9 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_225.1, data_11_225.2]

/-- Complete interval computation for depth 11, residue 226. -/
theorem bounds_11_226 : exactInterval 11 226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_226 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 226) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_226 : oddCount 226 11 = 2 ∧ acceleratedOrbit 11 226 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_226 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 226) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_226.1, data_11_226.2]

/-- Complete interval computation for depth 11, residue 227. -/
theorem bounds_11_227 : exactInterval 11 227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_227 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 227) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_227 : oddCount 227 11 = 2 ∧ acceleratedOrbit 11 227 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_227 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 227) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_227.1, data_11_227.2]

/-- Complete interval computation for depth 11, residue 228. -/
theorem bounds_11_228 : exactInterval 11 228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_228 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 228) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_228 : oddCount 228 11 = 5 ∧ acceleratedOrbit 11 228 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_228 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 228) = 3 ^ 5 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_228.1, data_11_228.2]

/-- Complete interval computation for depth 11, residue 229. -/
theorem bounds_11_229 : exactInterval 11 229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_229 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 229) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_229 : oddCount 229 11 = 5 ∧ acceleratedOrbit 11 229 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_229 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 229) = 3 ^ 5 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_229.1, data_11_229.2]

/-- Complete interval computation for depth 11, residue 230. -/
theorem bounds_11_230 : exactInterval 11 230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_230 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 230) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_230 : oddCount 230 11 = 5 ∧ acceleratedOrbit 11 230 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_230 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 230) = 3 ^ 5 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_230.1, data_11_230.2]

/-- Complete interval computation for depth 11, residue 231. -/
theorem bounds_11_231 : exactInterval 11 231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_231 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 231) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_231 : oddCount 231 11 = 7 ∧ acceleratedOrbit 11 231 = 248 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_231 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 231) = 3 ^ 7 * m + 248 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_231.1, data_11_231.2]

/-- Complete interval computation for depth 11, residue 232. -/
theorem bounds_11_232 : exactInterval 11 232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_232 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 232) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_232 : oddCount 232 11 = 4 ∧ acceleratedOrbit 11 232 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_232 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 232) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_232.1, data_11_232.2]

/-- Complete interval computation for depth 11, residue 233. -/
theorem bounds_11_233 : exactInterval 11 233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_233 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 233) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_233 : oddCount 233 11 = 7 ∧ acceleratedOrbit 11 233 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_233 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 233) = 3 ^ 7 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_233.1, data_11_233.2]

/-- Complete interval computation for depth 11, residue 234. -/
theorem bounds_11_234 : exactInterval 11 234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_234 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 234) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_234 : oddCount 234 11 = 4 ∧ acceleratedOrbit 11 234 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_234 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 234) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_234.1, data_11_234.2]

end Collatz.Research.StoppingAtlas.Batch0082
