import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch074

/-- Complete interval computation for depth 9, residue 236. -/
theorem bounds_9_236 : exactInterval 9 236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_236 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 236) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_236 : oddCount 236 9 = 4 ∧ acceleratedOrbit 9 236 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_236 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 236) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_236.1, data_9_236.2]

/-- Complete interval computation for depth 9, residue 237. -/
theorem bounds_9_237 : exactInterval 9 237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_237 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 237) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_237 : oddCount 237 9 = 4 ∧ acceleratedOrbit 9 237 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_237 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 237) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_237.1, data_9_237.2]

/-- Complete interval computation for depth 9, residue 238. -/
theorem bounds_9_238 : exactInterval 9 238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_238 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 238) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_238 : oddCount 238 9 = 4 ∧ acceleratedOrbit 9 238 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_238 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 238) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_238.1, data_9_238.2]

/-- Complete interval computation for depth 9, residue 239. -/
theorem bounds_9_239 : exactInterval 9 239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_239 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 239) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_239 : oddCount 239 9 = 8 ∧ acceleratedOrbit 9 239 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_239 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 239) = 3 ^ 8 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_239.1, data_9_239.2]

/-- Complete interval computation for depth 9, residue 240. -/
theorem bounds_9_240 : exactInterval 9 240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_240 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 240) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_240 : oddCount 240 9 = 4 ∧ acceleratedOrbit 9 240 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_240 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 240) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_240.1, data_9_240.2]

/-- Complete interval computation for depth 9, residue 241. -/
theorem bounds_9_241 : exactInterval 9 241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_241 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 241) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_241 : oddCount 241 9 = 3 ∧ acceleratedOrbit 9 241 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_241 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 241) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_241.1, data_9_241.2]

/-- Complete interval computation for depth 9, residue 242. -/
theorem bounds_9_242 : exactInterval 9 242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_242 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 242) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_242 : oddCount 242 9 = 6 ∧ acceleratedOrbit 9 242 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_242 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 242) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_242.1, data_9_242.2]

/-- Complete interval computation for depth 9, residue 243. -/
theorem bounds_9_243 : exactInterval 9 243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_243 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 243) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_243 : oddCount 243 9 = 6 ∧ acceleratedOrbit 9 243 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_243 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 243) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_243.1, data_9_243.2]

/-- Complete interval computation for depth 9, residue 244. -/
theorem bounds_9_244 : exactInterval 9 244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_244 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 244) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_244 : oddCount 244 9 = 4 ∧ acceleratedOrbit 9 244 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_244 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 244) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_244.1, data_9_244.2]

/-- Complete interval computation for depth 9, residue 245. -/
theorem bounds_9_245 : exactInterval 9 245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_245 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 245) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_245 : oddCount 245 9 = 4 ∧ acceleratedOrbit 9 245 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_245 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 245) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_245.1, data_9_245.2]

end Collatz.Research.DescentIntervals.Batch074
