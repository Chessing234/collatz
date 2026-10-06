import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0217

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 245. -/
theorem bounds_12_245 : exactInterval 12 245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_245 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 245) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_245 : oddCount 245 12 = 4 ∧ acceleratedOrbit 12 245 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_245 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 245) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_245.1, data_12_245.2]

/-- Complete interval computation for depth 12, residue 246. -/
theorem bounds_12_246 : exactInterval 12 246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_246 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 246) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_246 : oddCount 246 12 = 7 ∧ acceleratedOrbit 12 246 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_246 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 246) = 3 ^ 7 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_246.1, data_12_246.2]

/-- Complete interval computation for depth 12, residue 247. -/
theorem bounds_12_247 : exactInterval 12 247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_247 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 247) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_247 : oddCount 247 12 = 7 ∧ acceleratedOrbit 12 247 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_247 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 247) = 3 ^ 7 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_247.1, data_12_247.2]

/-- Complete interval computation for depth 12, residue 248. -/
theorem bounds_12_248 : exactInterval 12 248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_248 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 248) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_248 : oddCount 248 12 = 7 ∧ acceleratedOrbit 12 248 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_248 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 248) = 3 ^ 7 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_248.1, data_12_248.2]

/-- Complete interval computation for depth 12, residue 249. -/
theorem bounds_12_249 : exactInterval 12 249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_249 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 249) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_249 : oddCount 249 12 = 8 ∧ acceleratedOrbit 12 249 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_249 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 249) = 3 ^ 8 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_249.1, data_12_249.2]

/-- Complete interval computation for depth 12, residue 250. -/
theorem bounds_12_250 : exactInterval 12 250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_250 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 250) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_250 : oddCount 250 12 = 7 ∧ acceleratedOrbit 12 250 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_250 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 250) = 3 ^ 7 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_250.1, data_12_250.2]

/-- Complete interval computation for depth 12, residue 251. -/
theorem bounds_12_251 : exactInterval 12 251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_251 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 251) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_251 : oddCount 251 12 = 10 ∧ acceleratedOrbit 12 251 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_251 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 251) = 3 ^ 10 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_251.1, data_12_251.2]

/-- Complete interval computation for depth 12, residue 252. -/
theorem bounds_12_252 : exactInterval 12 252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_252 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 252) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_252 : oddCount 252 12 = 7 ∧ acceleratedOrbit 12 252 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_252 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 252) = 3 ^ 7 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_252.1, data_12_252.2]

/-- Complete interval computation for depth 12, residue 253. -/
theorem bounds_12_253 : exactInterval 12 253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_253 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 253) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_253 : oddCount 253 12 = 7 ∧ acceleratedOrbit 12 253 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_253 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 253) = 3 ^ 7 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_253.1, data_12_253.2]

/-- Complete interval computation for depth 12, residue 254. -/
theorem bounds_12_254 : exactInterval 12 254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_254 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 254) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_254 : oddCount 254 12 = 8 ∧ acceleratedOrbit 12 254 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_254 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 254) = 3 ^ 8 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_254.1, data_12_254.2]

/-- Complete interval computation for depth 12, residue 255. -/
theorem bounds_12_255 : exactInterval 12 255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_255 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 255) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_255 : oddCount 255 12 = 8 ∧ acceleratedOrbit 12 255 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_255 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 255) = 3 ^ 8 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_255.1, data_12_255.2]

/-- Complete interval computation for depth 12, residue 256. -/
theorem bounds_12_256 : exactInterval 12 256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_256 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 256) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_256 : oddCount 256 12 = 2 ∧ acceleratedOrbit 12 256 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_256 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 256) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_256.1, data_12_256.2]

/-- Complete interval computation for depth 12, residue 257. -/
theorem bounds_12_257 : exactInterval 12 257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_257 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 257) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_257 : oddCount 257 12 = 6 ∧ acceleratedOrbit 12 257 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_257 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 257) = 3 ^ 6 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_257.1, data_12_257.2]

/-- Complete interval computation for depth 12, residue 258. -/
theorem bounds_12_258 : exactInterval 12 258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_258 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 258) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_258 : oddCount 258 12 = 6 ∧ acceleratedOrbit 12 258 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_258 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 258) = 3 ^ 6 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_258.1, data_12_258.2]

/-- Complete interval computation for depth 12, residue 259. -/
theorem bounds_12_259 : exactInterval 12 259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_259 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 259) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_259 : oddCount 259 12 = 6 ∧ acceleratedOrbit 12 259 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_259 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 259) = 3 ^ 6 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_259.1, data_12_259.2]

/-- Complete interval computation for depth 12, residue 260. -/
theorem bounds_12_260 : exactInterval 12 260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_260 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 260) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_260 : oddCount 260 12 = 5 ∧ acceleratedOrbit 12 260 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_260 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 260) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_260.1, data_12_260.2]

end Collatz.Research.StoppingAtlas.Batch0217
