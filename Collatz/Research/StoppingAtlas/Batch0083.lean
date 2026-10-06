import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0083

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 235. -/
theorem bounds_11_235 : exactInterval 11 235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_235 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 235) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_235 : oddCount 235 11 = 7 ∧ acceleratedOrbit 11 235 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_235 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 235) = 3 ^ 7 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_235.1, data_11_235.2]

/-- Complete interval computation for depth 11, residue 236. -/
theorem bounds_11_236 : exactInterval 11 236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_236 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 236) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_236 : oddCount 236 11 = 5 ∧ acceleratedOrbit 11 236 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_236 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 236) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_236.1, data_11_236.2]

/-- Complete interval computation for depth 11, residue 237. -/
theorem bounds_11_237 : exactInterval 11 237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_237 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 237) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_237 : oddCount 237 11 = 5 ∧ acceleratedOrbit 11 237 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_237 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 237) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_237.1, data_11_237.2]

/-- Complete interval computation for depth 11, residue 238. -/
theorem bounds_11_238 : exactInterval 11 238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_238 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 238) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_238 : oddCount 238 11 = 5 ∧ acceleratedOrbit 11 238 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_238 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 238) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_238.1, data_11_238.2]

/-- Complete interval computation for depth 11, residue 239. -/
theorem bounds_11_239 : exactInterval 11 239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_239 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 239) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_239 : oddCount 239 11 = 9 ∧ acceleratedOrbit 11 239 = 2308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_239 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 239) = 3 ^ 9 * m + 2308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_239.1, data_11_239.2]

/-- Complete interval computation for depth 11, residue 240. -/
theorem bounds_11_240 : exactInterval 11 240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_240 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 240) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_240 : oddCount 240 11 = 4 ∧ acceleratedOrbit 11 240 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_240 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 240) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_240.1, data_11_240.2]

/-- Complete interval computation for depth 11, residue 241. -/
theorem bounds_11_241 : exactInterval 11 241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_241 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 241) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_241 : oddCount 241 11 = 4 ∧ acceleratedOrbit 11 241 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_241 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 241) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_241.1, data_11_241.2]

/-- Complete interval computation for depth 11, residue 242. -/
theorem bounds_11_242 : exactInterval 11 242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_242 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 242) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_242 : oddCount 242 11 = 7 ∧ acceleratedOrbit 11 242 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_242 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 242) = 3 ^ 7 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_242.1, data_11_242.2]

/-- Complete interval computation for depth 11, residue 243. -/
theorem bounds_11_243 : exactInterval 11 243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_243 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 243) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_243 : oddCount 243 11 = 7 ∧ acceleratedOrbit 11 243 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_243 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 243) = 3 ^ 7 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_243.1, data_11_243.2]

/-- Complete interval computation for depth 11, residue 244. -/
theorem bounds_11_244 : exactInterval 11 244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_244 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 244) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_244 : oddCount 244 11 = 4 ∧ acceleratedOrbit 11 244 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_244 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 244) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_244.1, data_11_244.2]

/-- Complete interval computation for depth 11, residue 245. -/
theorem bounds_11_245 : exactInterval 11 245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_245 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 245) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_245 : oddCount 245 11 = 4 ∧ acceleratedOrbit 11 245 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_245 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 245) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_245.1, data_11_245.2]

/-- Complete interval computation for depth 11, residue 246. -/
theorem bounds_11_246 : exactInterval 11 246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_246 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 246) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_246 : oddCount 246 11 = 6 ∧ acceleratedOrbit 11 246 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_246 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 246) = 3 ^ 6 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_246.1, data_11_246.2]

/-- Complete interval computation for depth 11, residue 247. -/
theorem bounds_11_247 : exactInterval 11 247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_247 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 247) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_247 : oddCount 247 11 = 6 ∧ acceleratedOrbit 11 247 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_247 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 247) = 3 ^ 6 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_247.1, data_11_247.2]

/-- Complete interval computation for depth 11, residue 248. -/
theorem bounds_11_248 : exactInterval 11 248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_248 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 248) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_248 : oddCount 248 11 = 6 ∧ acceleratedOrbit 11 248 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_248 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 248) = 3 ^ 6 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_248.1, data_11_248.2]

/-- Complete interval computation for depth 11, residue 249. -/
theorem bounds_11_249 : exactInterval 11 249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_249 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 249) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_249 : oddCount 249 11 = 7 ∧ acceleratedOrbit 11 249 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_249 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 249) = 3 ^ 7 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_249.1, data_11_249.2]

end Collatz.Research.StoppingAtlas.Batch0083
