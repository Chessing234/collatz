import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch049

/-- Complete interval computation for depth 8, residue 236. -/
theorem bounds_8_236 : exactInterval 8 236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_236 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 236) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_236 : oddCount 236 8 = 4 ∧ acceleratedOrbit 8 236 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_236 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 236) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_236.1, data_8_236.2]

/-- Complete interval computation for depth 8, residue 237. -/
theorem bounds_8_237 : exactInterval 8 237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_237 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 237) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_237 : oddCount 237 8 = 4 ∧ acceleratedOrbit 8 237 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_237 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 237) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_237.1, data_8_237.2]

/-- Complete interval computation for depth 8, residue 238. -/
theorem bounds_8_238 : exactInterval 8 238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_238 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 238) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_238 : oddCount 238 8 = 4 ∧ acceleratedOrbit 8 238 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_238 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 238) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_238.1, data_8_238.2]

/-- Complete interval computation for depth 8, residue 239. -/
theorem bounds_8_239 : exactInterval 8 239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_239 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 239) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_239 : oddCount 239 8 = 7 ∧ acceleratedOrbit 8 239 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_239 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 239) = 3 ^ 7 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_239.1, data_8_239.2]

/-- Complete interval computation for depth 8, residue 240. -/
theorem bounds_8_240 : exactInterval 8 240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_240 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 240) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_240 : oddCount 240 8 = 4 ∧ acceleratedOrbit 8 240 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_240 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 240) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_240.1, data_8_240.2]

/-- Complete interval computation for depth 8, residue 241. -/
theorem bounds_8_241 : exactInterval 8 241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_241 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 241) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_241 : oddCount 241 8 = 3 ∧ acceleratedOrbit 8 241 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_241 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 241) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_241.1, data_8_241.2]

/-- Complete interval computation for depth 8, residue 242. -/
theorem bounds_8_242 : exactInterval 8 242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_242 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 242) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_242 : oddCount 242 8 = 5 ∧ acceleratedOrbit 8 242 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_242 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 242) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_242.1, data_8_242.2]

/-- Complete interval computation for depth 8, residue 243. -/
theorem bounds_8_243 : exactInterval 8 243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_243 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 243) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_243 : oddCount 243 8 = 5 ∧ acceleratedOrbit 8 243 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_243 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 243) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_243.1, data_8_243.2]

/-- Complete interval computation for depth 8, residue 244. -/
theorem bounds_8_244 : exactInterval 8 244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_244 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 244) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_244 : oddCount 244 8 = 4 ∧ acceleratedOrbit 8 244 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_244 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 244) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_244.1, data_8_244.2]

/-- Complete interval computation for depth 8, residue 245. -/
theorem bounds_8_245 : exactInterval 8 245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_245 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 245) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_245 : oddCount 245 8 = 4 ∧ acceleratedOrbit 8 245 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_245 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 245) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_245.1, data_8_245.2]

end Collatz.Research.DescentIntervals.Batch049
