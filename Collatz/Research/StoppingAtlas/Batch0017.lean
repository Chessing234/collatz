import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0017

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 245. -/
theorem bounds_10_245 : exactInterval 10 245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_245 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 245) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_245 : oddCount 245 10 = 4 ∧ acceleratedOrbit 10 245 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_245 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 245) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_245.1, data_10_245.2]

/-- Complete interval computation for depth 10, residue 246. -/
theorem bounds_10_246 : exactInterval 10 246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_246 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 246) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_246 : oddCount 246 10 = 5 ∧ acceleratedOrbit 10 246 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_246 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 246) = 3 ^ 5 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_246.1, data_10_246.2]

/-- Complete interval computation for depth 10, residue 247. -/
theorem bounds_10_247 : exactInterval 10 247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_247 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 247) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_247 : oddCount 247 10 = 5 ∧ acceleratedOrbit 10 247 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_247 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 247) = 3 ^ 5 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_247.1, data_10_247.2]

/-- Complete interval computation for depth 10, residue 248. -/
theorem bounds_10_248 : exactInterval 10 248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_248 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 248) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_248 : oddCount 248 10 = 6 ∧ acceleratedOrbit 10 248 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_248 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 248) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_248.1, data_10_248.2]

/-- Complete interval computation for depth 10, residue 249. -/
theorem bounds_10_249 : exactInterval 10 249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_249 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 249) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_249 : oddCount 249 10 = 6 ∧ acceleratedOrbit 10 249 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_249 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 249) = 3 ^ 6 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_249.1, data_10_249.2]

/-- Complete interval computation for depth 10, residue 250. -/
theorem bounds_10_250 : exactInterval 10 250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_250 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 250) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_250 : oddCount 250 10 = 6 ∧ acceleratedOrbit 10 250 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_250 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 250) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_250.1, data_10_250.2]

/-- Complete interval computation for depth 10, residue 251. -/
theorem bounds_10_251 : exactInterval 10 251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_251 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 251) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_251 : oddCount 251 10 = 8 ∧ acceleratedOrbit 10 251 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_251 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 251) = 3 ^ 8 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_251.1, data_10_251.2]

/-- Complete interval computation for depth 10, residue 252. -/
theorem bounds_10_252 : exactInterval 10 252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_252 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 252) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_252 : oddCount 252 10 = 6 ∧ acceleratedOrbit 10 252 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_252 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 252) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_252.1, data_10_252.2]

/-- Complete interval computation for depth 10, residue 253. -/
theorem bounds_10_253 : exactInterval 10 253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_253 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 253) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_253 : oddCount 253 10 = 6 ∧ acceleratedOrbit 10 253 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_253 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 253) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_253.1, data_10_253.2]

/-- Complete interval computation for depth 10, residue 254. -/
theorem bounds_10_254 : exactInterval 10 254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_254 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 254) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_254 : oddCount 254 10 = 8 ∧ acceleratedOrbit 10 254 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_254 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 254) = 3 ^ 8 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_254.1, data_10_254.2]

/-- Complete interval computation for depth 10, residue 255. -/
theorem bounds_10_255 : exactInterval 10 255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_255 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 255) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_255 : oddCount 255 10 = 8 ∧ acceleratedOrbit 10 255 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_255 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 255) = 3 ^ 8 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_255.1, data_10_255.2]

/-- Complete interval computation for depth 10, residue 256. -/
theorem bounds_10_256 : exactInterval 10 256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_256 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 256) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_256 : oddCount 256 10 = 1 ∧ acceleratedOrbit 10 256 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_256 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 256) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_256.1, data_10_256.2]

/-- Complete interval computation for depth 10, residue 257. -/
theorem bounds_10_257 : exactInterval 10 257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_257 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 257) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_257 : oddCount 257 10 = 5 ∧ acceleratedOrbit 10 257 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_257 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 257) = 3 ^ 5 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_257.1, data_10_257.2]

/-- Complete interval computation for depth 10, residue 258. -/
theorem bounds_10_258 : exactInterval 10 258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_258 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 258) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_258 : oddCount 258 10 = 6 ∧ acceleratedOrbit 10 258 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_258 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 258) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_258.1, data_10_258.2]

/-- Complete interval computation for depth 10, residue 259. -/
theorem bounds_10_259 : exactInterval 10 259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_259 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 259) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_259 : oddCount 259 10 = 6 ∧ acceleratedOrbit 10 259 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_259 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 259) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_259.1, data_10_259.2]

/-- Complete interval computation for depth 10, residue 260. -/
theorem bounds_10_260 : exactInterval 10 260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_260 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 260) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_260 : oddCount 260 10 = 3 ∧ acceleratedOrbit 10 260 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_260 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 260) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_260.1, data_10_260.2]

end Collatz.Research.StoppingAtlas.Batch0017
