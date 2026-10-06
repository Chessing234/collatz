import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0008

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 229. -/
theorem bounds_15_229 : exactInterval 15 229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_229 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 229) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_229 : oddCount 229 15 = 7 ∧ acceleratedOrbit 15 229 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_229 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 229) = 3 ^ 7 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_229.1, data_15_229.2]

/-- Complete interval computation for depth 15, residue 230. -/
theorem bounds_15_230 : exactInterval 15 230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_230 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 230) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_230 : oddCount 230 15 = 7 ∧ acceleratedOrbit 15 230 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_230 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 230) = 3 ^ 7 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_230.1, data_15_230.2]

/-- Complete interval computation for depth 15, residue 231. -/
theorem bounds_15_231 : exactInterval 15 231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_231 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 231) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_231 : oddCount 231 15 = 8 ∧ acceleratedOrbit 15 231 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_231 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 231) = 3 ^ 8 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_231.1, data_15_231.2]

/-- Complete interval computation for depth 15, residue 232. -/
theorem bounds_15_232 : exactInterval 15 232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_232 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 232) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_232 : oddCount 232 15 = 5 ∧ acceleratedOrbit 15 232 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_232 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 232) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_232.1, data_15_232.2]

/-- Complete interval computation for depth 15, residue 233. -/
theorem bounds_15_233 : exactInterval 15 233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_233 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 233) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_233 : oddCount 233 15 = 10 ∧ acceleratedOrbit 15 233 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_233 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 233) = 3 ^ 10 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_233.1, data_15_233.2]

/-- Complete interval computation for depth 15, residue 234. -/
theorem bounds_15_234 : exactInterval 15 234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_234 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 234) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_234 : oddCount 234 15 = 5 ∧ acceleratedOrbit 15 234 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_234 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 234) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_234.1, data_15_234.2]

/-- Complete interval computation for depth 15, residue 235. -/
theorem bounds_15_235 : exactInterval 15 235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_235 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 235) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_235 : oddCount 235 15 = 9 ∧ acceleratedOrbit 15 235 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_235 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 235) = 3 ^ 9 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_235.1, data_15_235.2]

/-- Complete interval computation for depth 15, residue 236. -/
theorem bounds_15_236 : exactInterval 15 236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_236 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 236) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_236 : oddCount 236 15 = 7 ∧ acceleratedOrbit 15 236 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_236 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 236) = 3 ^ 7 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_236.1, data_15_236.2]

/-- Complete interval computation for depth 15, residue 237. -/
theorem bounds_15_237 : exactInterval 15 237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_237 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 237) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_237 : oddCount 237 15 = 7 ∧ acceleratedOrbit 15 237 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_237 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 237) = 3 ^ 7 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_237.1, data_15_237.2]

/-- Complete interval computation for depth 15, residue 238. -/
theorem bounds_15_238 : exactInterval 15 238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_238 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 238) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_238 : oddCount 238 15 = 7 ∧ acceleratedOrbit 15 238 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_238 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 238) = 3 ^ 7 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_238.1, data_15_238.2]

/-- Complete interval computation for depth 15, residue 239. -/
theorem bounds_15_239 : exactInterval 15 239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_239 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 239) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_239 : oddCount 239 15 = 10 ∧ acceleratedOrbit 15 239 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_239 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 239) = 3 ^ 10 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_239.1, data_15_239.2]

/-- Complete interval computation for depth 15, residue 240. -/
theorem bounds_15_240 : exactInterval 15 240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_240 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 240) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_240 : oddCount 240 15 = 5 ∧ acceleratedOrbit 15 240 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_240 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 240) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_240.1, data_15_240.2]

/-- Complete interval computation for depth 15, residue 241. -/
theorem bounds_15_241 : exactInterval 15 241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_241 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 241) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_241 : oddCount 241 15 = 5 ∧ acceleratedOrbit 15 241 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_241 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 241) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_241.1, data_15_241.2]

/-- Complete interval computation for depth 15, residue 242. -/
theorem bounds_15_242 : exactInterval 15 242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_242 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 242) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_242 : oddCount 242 15 = 10 ∧ acceleratedOrbit 15 242 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_242 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 242) = 3 ^ 10 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_242.1, data_15_242.2]

/-- Complete interval computation for depth 15, residue 243. -/
theorem bounds_15_243 : exactInterval 15 243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_243 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 243) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_243 : oddCount 243 15 = 10 ∧ acceleratedOrbit 15 243 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_243 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 243) = 3 ^ 10 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_243.1, data_15_243.2]

/-- Complete interval computation for depth 15, residue 244. -/
theorem bounds_15_244 : exactInterval 15 244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_244 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 244) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_244 : oddCount 244 15 = 5 ∧ acceleratedOrbit 15 244 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_244 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 244) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_244.1, data_15_244.2]

/-- Complete interval computation for depth 15, residue 245. -/
theorem bounds_15_245 : exactInterval 15 245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_245 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 245) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_245 : oddCount 245 15 = 5 ∧ acceleratedOrbit 15 245 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_245 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 245) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_245.1, data_15_245.2]

/-- Complete interval computation for depth 15, residue 246. -/
theorem bounds_15_246 : exactInterval 15 246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_246 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 246) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_246 : oddCount 246 15 = 9 ∧ acceleratedOrbit 15 246 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_246 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 246) = 3 ^ 9 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_246.1, data_15_246.2]

/-- Complete interval computation for depth 15, residue 247. -/
theorem bounds_15_247 : exactInterval 15 247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_247 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 247) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_247 : oddCount 247 15 = 9 ∧ acceleratedOrbit 15 247 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_247 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 247) = 3 ^ 9 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_247.1, data_15_247.2]

/-- Complete interval computation for depth 15, residue 248. -/
theorem bounds_15_248 : exactInterval 15 248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_248 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 248) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_248 : oddCount 248 15 = 9 ∧ acceleratedOrbit 15 248 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_248 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 248) = 3 ^ 9 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_248.1, data_15_248.2]

/-- Complete interval computation for depth 15, residue 249. -/
theorem bounds_15_249 : exactInterval 15 249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_249 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 249) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_249 : oddCount 249 15 = 9 ∧ acceleratedOrbit 15 249 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_249 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 249) = 3 ^ 9 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_249.1, data_15_249.2]

/-- Complete interval computation for depth 15, residue 250. -/
theorem bounds_15_250 : exactInterval 15 250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_250 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 250) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_250 : oddCount 250 15 = 9 ∧ acceleratedOrbit 15 250 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_250 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 250) = 3 ^ 9 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_250.1, data_15_250.2]

/-- Complete interval computation for depth 15, residue 251. -/
theorem bounds_15_251 : exactInterval 15 251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_251 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 251) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_251 : oddCount 251 15 = 11 ∧ acceleratedOrbit 15 251 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_251 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 251) = 3 ^ 11 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_251.1, data_15_251.2]

/-- Complete interval computation for depth 15, residue 252. -/
theorem bounds_15_252 : exactInterval 15 252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_252 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 252) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_252 : oddCount 252 15 = 9 ∧ acceleratedOrbit 15 252 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_252 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 252) = 3 ^ 9 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_252.1, data_15_252.2]

/-- Complete interval computation for depth 15, residue 253. -/
theorem bounds_15_253 : exactInterval 15 253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_253 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 253) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_253 : oddCount 253 15 = 9 ∧ acceleratedOrbit 15 253 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_253 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 253) = 3 ^ 9 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_253.1, data_15_253.2]

/-- Complete interval computation for depth 15, residue 254. -/
theorem bounds_15_254 : exactInterval 15 254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_254 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 254) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_254 : oddCount 254 15 = 9 ∧ acceleratedOrbit 15 254 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_254 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 254) = 3 ^ 9 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_254.1, data_15_254.2]

/-- Complete interval computation for depth 15, residue 255. -/
theorem bounds_15_255 : exactInterval 15 255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_255 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 255) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_255 : oddCount 255 15 = 9 ∧ acceleratedOrbit 15 255 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_255 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 255) = 3 ^ 9 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_255.1, data_15_255.2]

/-- Complete interval computation for depth 15, residue 256. -/
theorem bounds_15_256 : exactInterval 15 256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_256 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 256) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_256 : oddCount 256 15 = 4 ∧ acceleratedOrbit 15 256 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_256 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 256) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_256.1, data_15_256.2]

/-- Complete interval computation for depth 15, residue 257. -/
theorem bounds_15_257 : exactInterval 15 257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_257 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 257) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_257 : oddCount 257 15 = 9 ∧ acceleratedOrbit 15 257 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_257 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 257) = 3 ^ 9 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_257.1, data_15_257.2]

/-- Complete interval computation for depth 15, residue 258. -/
theorem bounds_15_258 : exactInterval 15 258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_258 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 258) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_258 : oddCount 258 15 = 9 ∧ acceleratedOrbit 15 258 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_258 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 258) = 3 ^ 9 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_258.1, data_15_258.2]

/-- Complete interval computation for depth 15, residue 259. -/
theorem bounds_15_259 : exactInterval 15 259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_259 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 259) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_259 : oddCount 259 15 = 9 ∧ acceleratedOrbit 15 259 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_259 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 259) = 3 ^ 9 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_259.1, data_15_259.2]

/-- Complete interval computation for depth 15, residue 260. -/
theorem bounds_15_260 : exactInterval 15 260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_260 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 260) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_260 : oddCount 260 15 = 7 ∧ acceleratedOrbit 15 260 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_260 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 260) = 3 ^ 7 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_260.1, data_15_260.2]

/-- Complete interval computation for depth 15, residue 261. -/
theorem bounds_15_261 : exactInterval 15 261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_261 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 261) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_261 : oddCount 261 15 = 7 ∧ acceleratedOrbit 15 261 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_261 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 261) = 3 ^ 7 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_261.1, data_15_261.2]

end Collatz.Research.PassageAtlas.Batch0008
