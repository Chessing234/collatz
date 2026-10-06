import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0016

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 230. -/
theorem bounds_10_230 : exactInterval 10 230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_230 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 230) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_230 : oddCount 230 10 = 5 ∧ acceleratedOrbit 10 230 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_230 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 230) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_230.1, data_10_230.2]

/-- Complete interval computation for depth 10, residue 231. -/
theorem bounds_10_231 : exactInterval 10 231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_231 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 231) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_231 : oddCount 231 10 = 7 ∧ acceleratedOrbit 10 231 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_231 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 231) = 3 ^ 7 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_231.1, data_10_231.2]

/-- Complete interval computation for depth 10, residue 232. -/
theorem bounds_10_232 : exactInterval 10 232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_232 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 232) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_232 : oddCount 232 10 = 4 ∧ acceleratedOrbit 10 232 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_232 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 232) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_232.1, data_10_232.2]

/-- Complete interval computation for depth 10, residue 233. -/
theorem bounds_10_233 : exactInterval 10 233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_233 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 233) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_233 : oddCount 233 10 = 6 ∧ acceleratedOrbit 10 233 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_233 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 233) = 3 ^ 6 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_233.1, data_10_233.2]

/-- Complete interval computation for depth 10, residue 234. -/
theorem bounds_10_234 : exactInterval 10 234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_234 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 234) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_234 : oddCount 234 10 = 4 ∧ acceleratedOrbit 10 234 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_234 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 234) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_234.1, data_10_234.2]

/-- Complete interval computation for depth 10, residue 235. -/
theorem bounds_10_235 : exactInterval 10 235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_235 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 235) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_235 : oddCount 235 10 = 7 ∧ acceleratedOrbit 10 235 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_235 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 235) = 3 ^ 7 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_235.1, data_10_235.2]

/-- Complete interval computation for depth 10, residue 236. -/
theorem bounds_10_236 : exactInterval 10 236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_236 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 236) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_236 : oddCount 236 10 = 4 ∧ acceleratedOrbit 10 236 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_236 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 236) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_236.1, data_10_236.2]

/-- Complete interval computation for depth 10, residue 237. -/
theorem bounds_10_237 : exactInterval 10 237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_237 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 237) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_237 : oddCount 237 10 = 4 ∧ acceleratedOrbit 10 237 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_237 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 237) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_237.1, data_10_237.2]

/-- Complete interval computation for depth 10, residue 238. -/
theorem bounds_10_238 : exactInterval 10 238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_238 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 238) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_238 : oddCount 238 10 = 4 ∧ acceleratedOrbit 10 238 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_238 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 238) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_238.1, data_10_238.2]

/-- Complete interval computation for depth 10, residue 239. -/
theorem bounds_10_239 : exactInterval 10 239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_239 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 239) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_239 : oddCount 239 10 = 9 ∧ acceleratedOrbit 10 239 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_239 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 239) = 3 ^ 9 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_239.1, data_10_239.2]

/-- Complete interval computation for depth 10, residue 240. -/
theorem bounds_10_240 : exactInterval 10 240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_240 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 240) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_240 : oddCount 240 10 = 4 ∧ acceleratedOrbit 10 240 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_240 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 240) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_240.1, data_10_240.2]

/-- Complete interval computation for depth 10, residue 241. -/
theorem bounds_10_241 : exactInterval 10 241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_241 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 241) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_241 : oddCount 241 10 = 4 ∧ acceleratedOrbit 10 241 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_241 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 241) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_241.1, data_10_241.2]

/-- Complete interval computation for depth 10, residue 242. -/
theorem bounds_10_242 : exactInterval 10 242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_242 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 242) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_242 : oddCount 242 10 = 6 ∧ acceleratedOrbit 10 242 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_242 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 242) = 3 ^ 6 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_242.1, data_10_242.2]

/-- Complete interval computation for depth 10, residue 243. -/
theorem bounds_10_243 : exactInterval 10 243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_243 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 243) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_243 : oddCount 243 10 = 6 ∧ acceleratedOrbit 10 243 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_243 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 243) = 3 ^ 6 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_243.1, data_10_243.2]

/-- Complete interval computation for depth 10, residue 244. -/
theorem bounds_10_244 : exactInterval 10 244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_244 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 244) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_244 : oddCount 244 10 = 4 ∧ acceleratedOrbit 10 244 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_244 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 244) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_244.1, data_10_244.2]

end Collatz.Research.StoppingAtlas.Batch0016
