import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0483

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 235. -/
theorem bounds_13_235 : exactInterval 13 235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_235 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 235) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_235 : oddCount 235 13 = 8 ∧ acceleratedOrbit 13 235 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_235 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 235) = 3 ^ 8 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_235.1, data_13_235.2]

/-- Complete interval computation for depth 13, residue 236. -/
theorem bounds_13_236 : exactInterval 13 236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_236 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 236) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_236 : oddCount 236 13 = 6 ∧ acceleratedOrbit 13 236 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_236 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 236) = 3 ^ 6 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_236.1, data_13_236.2]

/-- Complete interval computation for depth 13, residue 237. -/
theorem bounds_13_237 : exactInterval 13 237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_237 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 237) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_237 : oddCount 237 13 = 6 ∧ acceleratedOrbit 13 237 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_237 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 237) = 3 ^ 6 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_237.1, data_13_237.2]

/-- Complete interval computation for depth 13, residue 238. -/
theorem bounds_13_238 : exactInterval 13 238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_238 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 238) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_238 : oddCount 238 13 = 6 ∧ acceleratedOrbit 13 238 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_238 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 238) = 3 ^ 6 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_238.1, data_13_238.2]

/-- Complete interval computation for depth 13, residue 239. -/
theorem bounds_13_239 : exactInterval 13 239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_239 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 239) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_239 : oddCount 239 13 = 9 ∧ acceleratedOrbit 13 239 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_239 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 239) = 3 ^ 9 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_239.1, data_13_239.2]

/-- Complete interval computation for depth 13, residue 240. -/
theorem bounds_13_240 : exactInterval 13 240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_240 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 240) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_240 : oddCount 240 13 = 5 ∧ acceleratedOrbit 13 240 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_240 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 240) = 3 ^ 5 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_240.1, data_13_240.2]

/-- Complete interval computation for depth 13, residue 241. -/
theorem bounds_13_241 : exactInterval 13 241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_241 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 241) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_241 : oddCount 241 13 = 5 ∧ acceleratedOrbit 13 241 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_241 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 241) = 3 ^ 5 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_241.1, data_13_241.2]

/-- Complete interval computation for depth 13, residue 242. -/
theorem bounds_13_242 : exactInterval 13 242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_242 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 242) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_242 : oddCount 242 13 = 9 ∧ acceleratedOrbit 13 242 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_242 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 242) = 3 ^ 9 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_242.1, data_13_242.2]

/-- Complete interval computation for depth 13, residue 243. -/
theorem bounds_13_243 : exactInterval 13 243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_243 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 243) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_243 : oddCount 243 13 = 9 ∧ acceleratedOrbit 13 243 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_243 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 243) = 3 ^ 9 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_243.1, data_13_243.2]

/-- Complete interval computation for depth 13, residue 244. -/
theorem bounds_13_244 : exactInterval 13 244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_244 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 244) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_244 : oddCount 244 13 = 5 ∧ acceleratedOrbit 13 244 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_244 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 244) = 3 ^ 5 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_244.1, data_13_244.2]

/-- Complete interval computation for depth 13, residue 245. -/
theorem bounds_13_245 : exactInterval 13 245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_245 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 245) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_245 : oddCount 245 13 = 5 ∧ acceleratedOrbit 13 245 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_245 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 245) = 3 ^ 5 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_245.1, data_13_245.2]

/-- Complete interval computation for depth 13, residue 246. -/
theorem bounds_13_246 : exactInterval 13 246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_246 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 246) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_246 : oddCount 246 13 = 7 ∧ acceleratedOrbit 13 246 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_246 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 246) = 3 ^ 7 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_246.1, data_13_246.2]

/-- Complete interval computation for depth 13, residue 247. -/
theorem bounds_13_247 : exactInterval 13 247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_247 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 247) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_247 : oddCount 247 13 = 7 ∧ acceleratedOrbit 13 247 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_247 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 247) = 3 ^ 7 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_247.1, data_13_247.2]

/-- Complete interval computation for depth 13, residue 248. -/
theorem bounds_13_248 : exactInterval 13 248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_248 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 248) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_248 : oddCount 248 13 = 8 ∧ acceleratedOrbit 13 248 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_248 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 248) = 3 ^ 8 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_248.1, data_13_248.2]

/-- Complete interval computation for depth 13, residue 249. -/
theorem bounds_13_249 : exactInterval 13 249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_249 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 249) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_249 : oddCount 249 13 = 8 ∧ acceleratedOrbit 13 249 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_249 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 249) = 3 ^ 8 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_249.1, data_13_249.2]

end Collatz.Research.StoppingAtlas.Batch0483
