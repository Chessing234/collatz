import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0482

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 220. -/
theorem bounds_13_220 : exactInterval 13 220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_220 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 220) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_220 : oddCount 220 13 = 8 ∧ acceleratedOrbit 13 220 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_220 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 220) = 3 ^ 8 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_220.1, data_13_220.2]

/-- Complete interval computation for depth 13, residue 221. -/
theorem bounds_13_221 : exactInterval 13 221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_221 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 221) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_221 : oddCount 221 13 = 8 ∧ acceleratedOrbit 13 221 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_221 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 221) = 3 ^ 8 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_221.1, data_13_221.2]

/-- Complete interval computation for depth 13, residue 222. -/
theorem bounds_13_222 : exactInterval 13 222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_222 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 222) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_222 : oddCount 222 13 = 10 ∧ acceleratedOrbit 13 222 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_222 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 222) = 3 ^ 10 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_222.1, data_13_222.2]

/-- Complete interval computation for depth 13, residue 223. -/
theorem bounds_13_223 : exactInterval 13 223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_223 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 223) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_223 : oddCount 223 13 = 10 ∧ acceleratedOrbit 13 223 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_223 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 223) = 3 ^ 10 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_223.1, data_13_223.2]

/-- Complete interval computation for depth 13, residue 224. -/
theorem bounds_13_224 : exactInterval 13 224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_224 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 224) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_224 : oddCount 224 13 = 5 ∧ acceleratedOrbit 13 224 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_224 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 224) = 3 ^ 5 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_224.1, data_13_224.2]

/-- Complete interval computation for depth 13, residue 225. -/
theorem bounds_13_225 : exactInterval 13 225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_225 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 225) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_225 : oddCount 225 13 = 10 ∧ acceleratedOrbit 13 225 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_225 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 225) = 3 ^ 10 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_225.1, data_13_225.2]

/-- Complete interval computation for depth 13, residue 226. -/
theorem bounds_13_226 : exactInterval 13 226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_226 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 226) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_226 : oddCount 226 13 = 3 ∧ acceleratedOrbit 13 226 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_226 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 226) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_226.1, data_13_226.2]

/-- Complete interval computation for depth 13, residue 227. -/
theorem bounds_13_227 : exactInterval 13 227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_227 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 227) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_227 : oddCount 227 13 = 3 ∧ acceleratedOrbit 13 227 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_227 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 227) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_227.1, data_13_227.2]

/-- Complete interval computation for depth 13, residue 228. -/
theorem bounds_13_228 : exactInterval 13 228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_228 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 228) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_228 : oddCount 228 13 = 5 ∧ acceleratedOrbit 13 228 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_228 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 228) = 3 ^ 5 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_228.1, data_13_228.2]

/-- Complete interval computation for depth 13, residue 229. -/
theorem bounds_13_229 : exactInterval 13 229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_229 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 229) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_229 : oddCount 229 13 = 5 ∧ acceleratedOrbit 13 229 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_229 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 229) = 3 ^ 5 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_229.1, data_13_229.2]

/-- Complete interval computation for depth 13, residue 230. -/
theorem bounds_13_230 : exactInterval 13 230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_230 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 230) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_230 : oddCount 230 13 = 5 ∧ acceleratedOrbit 13 230 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_230 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 230) = 3 ^ 5 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_230.1, data_13_230.2]

/-- Complete interval computation for depth 13, residue 231. -/
theorem bounds_13_231 : exactInterval 13 231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_231 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 231) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_231 : oddCount 231 13 = 7 ∧ acceleratedOrbit 13 231 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_231 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 231) = 3 ^ 7 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_231.1, data_13_231.2]

/-- Complete interval computation for depth 13, residue 232. -/
theorem bounds_13_232 : exactInterval 13 232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_232 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 232) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_232 : oddCount 232 13 = 5 ∧ acceleratedOrbit 13 232 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_232 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 232) = 3 ^ 5 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_232.1, data_13_232.2]

/-- Complete interval computation for depth 13, residue 233. -/
theorem bounds_13_233 : exactInterval 13 233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_233 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 233) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_233 : oddCount 233 13 = 9 ∧ acceleratedOrbit 13 233 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_233 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 233) = 3 ^ 9 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_233.1, data_13_233.2]

/-- Complete interval computation for depth 13, residue 234. -/
theorem bounds_13_234 : exactInterval 13 234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_234 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 234) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_234 : oddCount 234 13 = 5 ∧ acceleratedOrbit 13 234 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_234 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 234) = 3 ^ 5 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_234.1, data_13_234.2]

end Collatz.Research.StoppingAtlas.Batch0482
