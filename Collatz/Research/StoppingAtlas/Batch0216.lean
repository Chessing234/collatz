import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0216

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 230. -/
theorem bounds_12_230 : exactInterval 12 230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_230 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 230) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_230 : oddCount 230 12 = 5 ∧ acceleratedOrbit 12 230 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_230 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 230) = 3 ^ 5 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_230.1, data_12_230.2]

/-- Complete interval computation for depth 12, residue 231. -/
theorem bounds_12_231 : exactInterval 12 231 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_231 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 231) 12 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_231 : oddCount 231 12 = 7 ∧ acceleratedOrbit 12 231 = 124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_231 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 231) = 3 ^ 7 * m + 124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_231.1, data_12_231.2]

/-- Complete interval computation for depth 12, residue 232. -/
theorem bounds_12_232 : exactInterval 12 232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_232 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 232) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_232 : oddCount 232 12 = 4 ∧ acceleratedOrbit 12 232 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_232 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 232) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_232.1, data_12_232.2]

/-- Complete interval computation for depth 12, residue 233. -/
theorem bounds_12_233 : exactInterval 12 233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_233 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 233) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_233 : oddCount 233 12 = 8 ∧ acceleratedOrbit 12 233 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_233 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 233) = 3 ^ 8 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_233.1, data_12_233.2]

/-- Complete interval computation for depth 12, residue 234. -/
theorem bounds_12_234 : exactInterval 12 234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_234 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 234) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_234 : oddCount 234 12 = 4 ∧ acceleratedOrbit 12 234 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_234 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 234) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_234.1, data_12_234.2]

/-- Complete interval computation for depth 12, residue 235. -/
theorem bounds_12_235 : exactInterval 12 235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_235 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 235) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_235 : oddCount 235 12 = 8 ∧ acceleratedOrbit 12 235 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_235 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 235) = 3 ^ 8 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_235.1, data_12_235.2]

/-- Complete interval computation for depth 12, residue 236. -/
theorem bounds_12_236 : exactInterval 12 236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_236 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 236) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_236 : oddCount 236 12 = 6 ∧ acceleratedOrbit 12 236 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_236 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 236) = 3 ^ 6 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_236.1, data_12_236.2]

/-- Complete interval computation for depth 12, residue 237. -/
theorem bounds_12_237 : exactInterval 12 237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_237 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 237) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_237 : oddCount 237 12 = 6 ∧ acceleratedOrbit 12 237 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_237 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 237) = 3 ^ 6 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_237.1, data_12_237.2]

/-- Complete interval computation for depth 12, residue 238. -/
theorem bounds_12_238 : exactInterval 12 238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_238 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 238) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_238 : oddCount 238 12 = 6 ∧ acceleratedOrbit 12 238 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_238 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 238) = 3 ^ 6 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_238.1, data_12_238.2]

/-- Complete interval computation for depth 12, residue 239. -/
theorem bounds_12_239 : exactInterval 12 239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_239 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 239) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_239 : oddCount 239 12 = 9 ∧ acceleratedOrbit 12 239 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_239 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 239) = 3 ^ 9 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_239.1, data_12_239.2]

/-- Complete interval computation for depth 12, residue 240. -/
theorem bounds_12_240 : exactInterval 12 240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_240 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 240) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_240 : oddCount 240 12 = 4 ∧ acceleratedOrbit 12 240 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_240 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 240) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_240.1, data_12_240.2]

/-- Complete interval computation for depth 12, residue 241. -/
theorem bounds_12_241 : exactInterval 12 241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_241 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 241) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_241 : oddCount 241 12 = 4 ∧ acceleratedOrbit 12 241 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_241 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 241) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_241.1, data_12_241.2]

/-- Complete interval computation for depth 12, residue 242. -/
theorem bounds_12_242 : exactInterval 12 242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_242 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 242) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_242 : oddCount 242 12 = 8 ∧ acceleratedOrbit 12 242 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_242 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 242) = 3 ^ 8 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_242.1, data_12_242.2]

/-- Complete interval computation for depth 12, residue 243. -/
theorem bounds_12_243 : exactInterval 12 243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_243 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 243) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_243 : oddCount 243 12 = 8 ∧ acceleratedOrbit 12 243 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_243 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 243) = 3 ^ 8 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_243.1, data_12_243.2]

/-- Complete interval computation for depth 12, residue 244. -/
theorem bounds_12_244 : exactInterval 12 244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_244 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 244) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_244 : oddCount 244 12 = 4 ∧ acceleratedOrbit 12 244 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_244 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 244) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_244.1, data_12_244.2]

end Collatz.Research.StoppingAtlas.Batch0216
