import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch046

/-- Complete interval computation for depth 8, residue 205. -/
theorem bounds_8_205 : exactInterval 8 205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_205 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 205) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_205 : oddCount 205 8 = 3 ∧ acceleratedOrbit 8 205 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_205 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 205) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_205.1, data_8_205.2]

/-- Complete interval computation for depth 8, residue 206. -/
theorem bounds_8_206 : exactInterval 8 206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_206 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 206) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_206 : oddCount 206 8 = 6 ∧ acceleratedOrbit 8 206 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_206 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 206) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_206.1, data_8_206.2]

/-- Complete interval computation for depth 8, residue 207. -/
theorem bounds_8_207 : exactInterval 8 207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_207 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 207) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_207 : oddCount 207 8 = 6 ∧ acceleratedOrbit 8 207 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_207 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 207) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_207.1, data_8_207.2]

/-- Complete interval computation for depth 8, residue 208. -/
theorem bounds_8_208 : exactInterval 8 208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_208 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 208) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_208 : oddCount 208 8 = 2 ∧ acceleratedOrbit 8 208 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_208 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 208) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_208.1, data_8_208.2]

/-- Complete interval computation for depth 8, residue 209. -/
theorem bounds_8_209 : exactInterval 8 209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_209 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 209) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_209 : oddCount 209 8 = 4 ∧ acceleratedOrbit 8 209 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_209 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 209) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_209.1, data_8_209.2]

/-- Complete interval computation for depth 8, residue 210. -/
theorem bounds_8_210 : exactInterval 8 210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_210 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 210) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_210 : oddCount 210 8 = 5 ∧ acceleratedOrbit 8 210 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_210 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 210) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_210.1, data_8_210.2]

/-- Complete interval computation for depth 8, residue 211. -/
theorem bounds_8_211 : exactInterval 8 211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_211 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 211) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_211 : oddCount 211 8 = 5 ∧ acceleratedOrbit 8 211 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_211 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 211) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_211.1, data_8_211.2]

/-- Complete interval computation for depth 8, residue 212. -/
theorem bounds_8_212 : exactInterval 8 212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_212 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 212) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_212 : oddCount 212 8 = 2 ∧ acceleratedOrbit 8 212 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_212 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 212) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_212.1, data_8_212.2]

/-- Complete interval computation for depth 8, residue 213. -/
theorem bounds_8_213 : exactInterval 8 213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_213 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 213) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_213 : oddCount 213 8 = 2 ∧ acceleratedOrbit 8 213 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_213 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 213) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_213.1, data_8_213.2]

/-- Complete interval computation for depth 8, residue 214. -/
theorem bounds_8_214 : exactInterval 8 214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_214 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 214) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_214 : oddCount 214 8 = 5 ∧ acceleratedOrbit 8 214 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_214 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 214) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_214.1, data_8_214.2]

/-- Complete interval computation for depth 8, residue 215. -/
theorem bounds_8_215 : exactInterval 8 215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_215 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 215) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_215 : oddCount 215 8 = 5 ∧ acceleratedOrbit 8 215 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_215 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 215) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_215.1, data_8_215.2]

end Collatz.Research.DescentIntervals.Batch046
