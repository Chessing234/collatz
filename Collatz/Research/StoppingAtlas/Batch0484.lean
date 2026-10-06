import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0484

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 250. -/
theorem bounds_13_250 : exactInterval 13 250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_250 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 250) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_250 : oddCount 250 13 = 8 ∧ acceleratedOrbit 13 250 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_250 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 250) = 3 ^ 8 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_250.1, data_13_250.2]

/-- Complete interval computation for depth 13, residue 251. -/
theorem bounds_13_251 : exactInterval 13 251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_251 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 251) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_251 : oddCount 251 13 = 10 ∧ acceleratedOrbit 13 251 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_251 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 251) = 3 ^ 10 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_251.1, data_13_251.2]

/-- Complete interval computation for depth 13, residue 252. -/
theorem bounds_13_252 : exactInterval 13 252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_252 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 252) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_252 : oddCount 252 13 = 8 ∧ acceleratedOrbit 13 252 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_252 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 252) = 3 ^ 8 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_252.1, data_13_252.2]

/-- Complete interval computation for depth 13, residue 253. -/
theorem bounds_13_253 : exactInterval 13 253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_253 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 253) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_253 : oddCount 253 13 = 8 ∧ acceleratedOrbit 13 253 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_253 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 253) = 3 ^ 8 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_253.1, data_13_253.2]

/-- Complete interval computation for depth 13, residue 254. -/
theorem bounds_13_254 : exactInterval 13 254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_254 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 254) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_254 : oddCount 254 13 = 8 ∧ acceleratedOrbit 13 254 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_254 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 254) = 3 ^ 8 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_254.1, data_13_254.2]

/-- Complete interval computation for depth 13, residue 255. -/
theorem bounds_13_255 : exactInterval 13 255 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_255 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 255) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_255 : oddCount 255 13 = 8 ∧ acceleratedOrbit 13 255 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_255 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 255) = 3 ^ 8 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_255.1, data_13_255.2]

/-- Complete interval computation for depth 13, residue 256. -/
theorem bounds_13_256 : exactInterval 13 256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_256 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 256) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_256 : oddCount 256 13 = 3 ∧ acceleratedOrbit 13 256 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_256 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 256) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_256.1, data_13_256.2]

/-- Complete interval computation for depth 13, residue 257. -/
theorem bounds_13_257 : exactInterval 13 257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_257 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 257) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_257 : oddCount 257 13 = 7 ∧ acceleratedOrbit 13 257 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_257 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 257) = 3 ^ 7 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_257.1, data_13_257.2]

/-- Complete interval computation for depth 13, residue 258. -/
theorem bounds_13_258 : exactInterval 13 258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_258 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 258) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_258 : oddCount 258 13 = 7 ∧ acceleratedOrbit 13 258 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_258 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 258) = 3 ^ 7 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_258.1, data_13_258.2]

/-- Complete interval computation for depth 13, residue 259. -/
theorem bounds_13_259 : exactInterval 13 259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_259 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 259) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_259 : oddCount 259 13 = 7 ∧ acceleratedOrbit 13 259 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_259 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 259) = 3 ^ 7 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_259.1, data_13_259.2]

/-- Complete interval computation for depth 13, residue 260. -/
theorem bounds_13_260 : exactInterval 13 260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_260 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 260) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_260 : oddCount 260 13 = 6 ∧ acceleratedOrbit 13 260 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_260 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 260) = 3 ^ 6 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_260.1, data_13_260.2]

/-- Complete interval computation for depth 13, residue 261. -/
theorem bounds_13_261 : exactInterval 13 261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_261 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 261) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_261 : oddCount 261 13 = 6 ∧ acceleratedOrbit 13 261 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_261 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 261) = 3 ^ 6 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_261.1, data_13_261.2]

/-- Complete interval computation for depth 13, residue 262. -/
theorem bounds_13_262 : exactInterval 13 262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_262 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 262) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_262 : oddCount 262 13 = 6 ∧ acceleratedOrbit 13 262 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_262 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 262) = 3 ^ 6 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_262.1, data_13_262.2]

/-- Complete interval computation for depth 13, residue 263. -/
theorem bounds_13_263 : exactInterval 13 263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_263 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 263) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_263 : oddCount 263 13 = 9 ∧ acceleratedOrbit 13 263 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_263 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 263) = 3 ^ 9 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_263.1, data_13_263.2]

/-- Complete interval computation for depth 13, residue 264. -/
theorem bounds_13_264 : exactInterval 13 264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_264 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 264) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_264 : oddCount 264 13 = 6 ∧ acceleratedOrbit 13 264 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_264 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 264) = 3 ^ 6 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_264.1, data_13_264.2]

/-- Complete interval computation for depth 13, residue 265. -/
theorem bounds_13_265 : exactInterval 13 265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_265 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 265) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_265 : oddCount 265 13 = 8 ∧ acceleratedOrbit 13 265 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_265 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 265) = 3 ^ 8 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_265.1, data_13_265.2]

end Collatz.Research.StoppingAtlas.Batch0484
