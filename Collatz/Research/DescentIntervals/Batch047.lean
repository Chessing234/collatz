import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch047

/-- Complete interval computation for depth 8, residue 216. -/
theorem bounds_8_216 : exactInterval 8 216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_216 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 216) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_216 : oddCount 216 8 = 4 ∧ acceleratedOrbit 8 216 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_216 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 216) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_216.1, data_8_216.2]

/-- Complete interval computation for depth 8, residue 217. -/
theorem bounds_8_217 : exactInterval 8 217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_217 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 217) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_217 : oddCount 217 8 = 3 ∧ acceleratedOrbit 8 217 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_217 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 217) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_217.1, data_8_217.2]

/-- Complete interval computation for depth 8, residue 218. -/
theorem bounds_8_218 : exactInterval 8 218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_218 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 218) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_218 : oddCount 218 8 = 4 ∧ acceleratedOrbit 8 218 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_218 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 218) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_218.1, data_8_218.2]

/-- Complete interval computation for depth 8, residue 219. -/
theorem bounds_8_219 : exactInterval 8 219 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_219 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 219) 8 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_219 : oddCount 219 8 = 5 ∧ acceleratedOrbit 8 219 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_219 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 219) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_219.1, data_8_219.2]

/-- Complete interval computation for depth 8, residue 220. -/
theorem bounds_8_220 : exactInterval 8 220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_220 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 220) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_220 : oddCount 220 8 = 4 ∧ acceleratedOrbit 8 220 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_220 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 220) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_220.1, data_8_220.2]

/-- Complete interval computation for depth 8, residue 221. -/
theorem bounds_8_221 : exactInterval 8 221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_221 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 221) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_221 : oddCount 221 8 = 4 ∧ acceleratedOrbit 8 221 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_221 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 221) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_221.1, data_8_221.2]

/-- Complete interval computation for depth 8, residue 222. -/
theorem bounds_8_222 : exactInterval 8 222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_222 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 222) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_222 : oddCount 222 8 = 6 ∧ acceleratedOrbit 8 222 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_222 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 222) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_222.1, data_8_222.2]

/-- Complete interval computation for depth 8, residue 223. -/
theorem bounds_8_223 : exactInterval 8 223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_223 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 223) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_223 : oddCount 223 8 = 6 ∧ acceleratedOrbit 8 223 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_223 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 223) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_223.1, data_8_223.2]

/-- Complete interval computation for depth 8, residue 224. -/
theorem bounds_8_224 : exactInterval 8 224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_224 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 224) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_224 : oddCount 224 8 = 3 ∧ acceleratedOrbit 8 224 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_224 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 224) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_224.1, data_8_224.2]

/-- Complete interval computation for depth 8, residue 225. -/
theorem bounds_8_225 : exactInterval 8 225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_225 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 225) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_225 : oddCount 225 8 = 6 ∧ acceleratedOrbit 8 225 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_225 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 225) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_225.1, data_8_225.2]

end Collatz.Research.DescentIntervals.Batch047
