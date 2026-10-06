import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0084

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 250. -/
theorem bounds_11_250 : exactInterval 11 250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_250 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 250) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_250 : oddCount 250 11 = 6 ∧ acceleratedOrbit 11 250 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_250 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 250) = 3 ^ 6 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_250.1, data_11_250.2]

/-- Complete interval computation for depth 11, residue 251. -/
theorem bounds_11_251 : exactInterval 11 251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_251 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 251) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_251 : oddCount 251 11 = 9 ∧ acceleratedOrbit 11 251 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_251 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 251) = 3 ^ 9 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_251.1, data_11_251.2]

/-- Complete interval computation for depth 11, residue 252. -/
theorem bounds_11_252 : exactInterval 11 252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_252 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 252) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_252 : oddCount 252 11 = 6 ∧ acceleratedOrbit 11 252 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_252 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 252) = 3 ^ 6 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_252.1, data_11_252.2]

/-- Complete interval computation for depth 11, residue 253. -/
theorem bounds_11_253 : exactInterval 11 253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_253 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 253) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_253 : oddCount 253 11 = 6 ∧ acceleratedOrbit 11 253 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_253 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 253) = 3 ^ 6 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_253.1, data_11_253.2]

/-- Complete interval computation for depth 11, residue 254. -/
theorem bounds_11_254 : exactInterval 11 254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_254 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 254) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_254 : oddCount 254 11 = 8 ∧ acceleratedOrbit 11 254 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_254 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 254) = 3 ^ 8 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_254.1, data_11_254.2]

/-- Complete interval computation for depth 11, residue 255. -/
theorem bounds_11_255 : exactInterval 11 255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_255 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 255) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_255 : oddCount 255 11 = 8 ∧ acceleratedOrbit 11 255 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_255 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 255) = 3 ^ 8 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_255.1, data_11_255.2]

/-- Complete interval computation for depth 11, residue 256. -/
theorem bounds_11_256 : exactInterval 11 256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_256 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 256) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_256 : oddCount 256 11 = 2 ∧ acceleratedOrbit 11 256 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_256 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 256) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_256.1, data_11_256.2]

/-- Complete interval computation for depth 11, residue 257. -/
theorem bounds_11_257 : exactInterval 11 257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_257 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 257) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_257 : oddCount 257 11 = 5 ∧ acceleratedOrbit 11 257 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_257 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 257) = 3 ^ 5 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_257.1, data_11_257.2]

/-- Complete interval computation for depth 11, residue 258. -/
theorem bounds_11_258 : exactInterval 11 258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_258 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 258) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_258 : oddCount 258 11 = 6 ∧ acceleratedOrbit 11 258 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_258 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 258) = 3 ^ 6 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_258.1, data_11_258.2]

/-- Complete interval computation for depth 11, residue 259. -/
theorem bounds_11_259 : exactInterval 11 259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_259 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 259) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_259 : oddCount 259 11 = 6 ∧ acceleratedOrbit 11 259 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_259 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 259) = 3 ^ 6 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_259.1, data_11_259.2]

/-- Complete interval computation for depth 11, residue 260. -/
theorem bounds_11_260 : exactInterval 11 260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_260 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 260) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_260 : oddCount 260 11 = 4 ∧ acceleratedOrbit 11 260 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_260 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 260) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_260.1, data_11_260.2]

/-- Complete interval computation for depth 11, residue 261. -/
theorem bounds_11_261 : exactInterval 11 261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_261 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 261) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_261 : oddCount 261 11 = 4 ∧ acceleratedOrbit 11 261 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_261 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 261) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_261.1, data_11_261.2]

/-- Complete interval computation for depth 11, residue 262. -/
theorem bounds_11_262 : exactInterval 11 262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_262 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 262) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_262 : oddCount 262 11 = 4 ∧ acceleratedOrbit 11 262 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_262 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 262) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_262.1, data_11_262.2]

/-- Complete interval computation for depth 11, residue 263. -/
theorem bounds_11_263 : exactInterval 11 263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_263 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 263) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_263 : oddCount 263 11 = 7 ∧ acceleratedOrbit 11 263 = 283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_263 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 263) = 3 ^ 7 * m + 283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_263.1, data_11_263.2]

/-- Complete interval computation for depth 11, residue 264. -/
theorem bounds_11_264 : exactInterval 11 264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_264 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 264) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_264 : oddCount 264 11 = 4 ∧ acceleratedOrbit 11 264 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_264 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 264) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_264.1, data_11_264.2]

/-- Complete interval computation for depth 11, residue 265. -/
theorem bounds_11_265 : exactInterval 11 265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_265 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 265) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_265 : oddCount 265 11 = 6 ∧ acceleratedOrbit 11 265 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_265 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 265) = 3 ^ 6 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_265.1, data_11_265.2]

end Collatz.Research.StoppingAtlas.Batch0084
