import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch072

/-- Complete interval computation for depth 9, residue 215. -/
theorem bounds_9_215 : exactInterval 9 215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_215 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 215) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_215 : oddCount 215 9 = 5 ∧ acceleratedOrbit 9 215 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_215 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 215) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_215.1, data_9_215.2]

/-- Complete interval computation for depth 9, residue 216. -/
theorem bounds_9_216 : exactInterval 9 216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_216 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 216) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_216 : oddCount 216 9 = 5 ∧ acceleratedOrbit 9 216 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_216 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 216) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_216.1, data_9_216.2]

/-- Complete interval computation for depth 9, residue 217. -/
theorem bounds_9_217 : exactInterval 9 217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_217 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 217) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_217 : oddCount 217 9 = 4 ∧ acceleratedOrbit 9 217 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_217 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 217) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_217.1, data_9_217.2]

/-- Complete interval computation for depth 9, residue 218. -/
theorem bounds_9_218 : exactInterval 9 218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_218 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 218) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_218 : oddCount 218 9 = 5 ∧ acceleratedOrbit 9 218 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_218 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 218) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_218.1, data_9_218.2]

/-- Complete interval computation for depth 9, residue 219. -/
theorem bounds_9_219 : exactInterval 9 219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_219 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 219) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_219 : oddCount 219 9 = 6 ∧ acceleratedOrbit 9 219 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_219 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 219) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_219.1, data_9_219.2]

/-- Complete interval computation for depth 9, residue 220. -/
theorem bounds_9_220 : exactInterval 9 220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_220 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 220) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_220 : oddCount 220 9 = 5 ∧ acceleratedOrbit 9 220 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_220 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 220) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_220.1, data_9_220.2]

/-- Complete interval computation for depth 9, residue 221. -/
theorem bounds_9_221 : exactInterval 9 221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_221 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 221) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_221 : oddCount 221 9 = 5 ∧ acceleratedOrbit 9 221 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_221 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 221) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_221.1, data_9_221.2]

/-- Complete interval computation for depth 9, residue 222. -/
theorem bounds_9_222 : exactInterval 9 222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_222 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 222) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_222 : oddCount 222 9 = 6 ∧ acceleratedOrbit 9 222 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_222 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 222) = 3 ^ 6 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_222.1, data_9_222.2]

/-- Complete interval computation for depth 9, residue 223. -/
theorem bounds_9_223 : exactInterval 9 223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_223 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 223) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_223 : oddCount 223 9 = 6 ∧ acceleratedOrbit 9 223 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_223 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 223) = 3 ^ 6 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_223.1, data_9_223.2]

/-- Complete interval computation for depth 9, residue 224. -/
theorem bounds_9_224 : exactInterval 9 224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_224 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 224) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_224 : oddCount 224 9 = 3 ∧ acceleratedOrbit 9 224 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_224 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 224) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_224.1, data_9_224.2]

end Collatz.Research.DescentIntervals.Batch072
