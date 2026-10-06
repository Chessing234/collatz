import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch071

/-- Complete interval computation for depth 9, residue 205. -/
theorem bounds_9_205 : exactInterval 9 205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_205 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 205) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_205 : oddCount 205 9 = 3 ∧ acceleratedOrbit 9 205 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_205 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 205) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_205.1, data_9_205.2]

/-- Complete interval computation for depth 9, residue 206. -/
theorem bounds_9_206 : exactInterval 9 206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_206 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 206) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_206 : oddCount 206 9 = 7 ∧ acceleratedOrbit 9 206 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_206 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 206) = 3 ^ 7 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_206.1, data_9_206.2]

/-- Complete interval computation for depth 9, residue 207. -/
theorem bounds_9_207 : exactInterval 9 207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_207 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 207) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_207 : oddCount 207 9 = 7 ∧ acceleratedOrbit 9 207 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_207 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 207) = 3 ^ 7 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_207.1, data_9_207.2]

/-- Complete interval computation for depth 9, residue 208. -/
theorem bounds_9_208 : exactInterval 9 208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_208 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 208) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_208 : oddCount 208 9 = 2 ∧ acceleratedOrbit 9 208 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_208 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 208) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_208.1, data_9_208.2]

/-- Complete interval computation for depth 9, residue 209. -/
theorem bounds_9_209 : exactInterval 9 209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_209 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 209) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_209 : oddCount 209 9 = 5 ∧ acceleratedOrbit 9 209 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_209 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 209) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_209.1, data_9_209.2]

/-- Complete interval computation for depth 9, residue 210. -/
theorem bounds_9_210 : exactInterval 9 210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_210 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 210) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_210 : oddCount 210 9 = 5 ∧ acceleratedOrbit 9 210 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_210 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 210) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_210.1, data_9_210.2]

/-- Complete interval computation for depth 9, residue 211. -/
theorem bounds_9_211 : exactInterval 9 211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_211 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 211) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_211 : oddCount 211 9 = 5 ∧ acceleratedOrbit 9 211 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_211 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 211) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_211.1, data_9_211.2]

/-- Complete interval computation for depth 9, residue 212. -/
theorem bounds_9_212 : exactInterval 9 212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_212 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 212) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_212 : oddCount 212 9 = 2 ∧ acceleratedOrbit 9 212 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_212 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 212) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_212.1, data_9_212.2]

/-- Complete interval computation for depth 9, residue 213. -/
theorem bounds_9_213 : exactInterval 9 213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_213 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 213) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_213 : oddCount 213 9 = 2 ∧ acceleratedOrbit 9 213 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_213 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 213) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_213.1, data_9_213.2]

/-- Complete interval computation for depth 9, residue 214. -/
theorem bounds_9_214 : exactInterval 9 214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_214 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 214) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_214 : oddCount 214 9 = 5 ∧ acceleratedOrbit 9 214 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_214 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 214) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_214.1, data_9_214.2]

end Collatz.Research.DescentIntervals.Batch071
