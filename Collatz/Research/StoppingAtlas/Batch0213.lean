import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0213

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 184. -/
theorem bounds_12_184 : exactInterval 12 184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_184 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 184) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_184 : oddCount 184 12 = 4 ∧ acceleratedOrbit 12 184 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_184 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 184) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_184.1, data_12_184.2]

/-- Complete interval computation for depth 12, residue 185. -/
theorem bounds_12_185 : exactInterval 12 185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_185 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 185) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_185 : oddCount 185 12 = 7 ∧ acceleratedOrbit 12 185 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_185 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 185) = 3 ^ 7 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_185.1, data_12_185.2]

/-- Complete interval computation for depth 12, residue 186. -/
theorem bounds_12_186 : exactInterval 12 186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_186 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 186) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_186 : oddCount 186 12 = 4 ∧ acceleratedOrbit 12 186 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_186 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 186) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_186.1, data_12_186.2]

/-- Complete interval computation for depth 12, residue 187. -/
theorem bounds_12_187 : exactInterval 12 187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_187 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 187) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_187 : oddCount 187 12 = 7 ∧ acceleratedOrbit 12 187 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_187 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 187) = 3 ^ 7 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_187.1, data_12_187.2]

/-- Complete interval computation for depth 12, residue 188. -/
theorem bounds_12_188 : exactInterval 12 188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_188 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 188) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_188 : oddCount 188 12 = 7 ∧ acceleratedOrbit 12 188 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_188 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 188) = 3 ^ 7 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_188.1, data_12_188.2]

/-- Complete interval computation for depth 12, residue 189. -/
theorem bounds_12_189 : exactInterval 12 189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_189 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 189) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_189 : oddCount 189 12 = 7 ∧ acceleratedOrbit 12 189 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_189 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 189) = 3 ^ 7 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_189.1, data_12_189.2]

/-- Complete interval computation for depth 12, residue 190. -/
theorem bounds_12_190 : exactInterval 12 190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_190 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 190) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_190 : oddCount 190 12 = 7 ∧ acceleratedOrbit 12 190 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_190 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 190) = 3 ^ 7 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_190.1, data_12_190.2]

/-- Complete interval computation for depth 12, residue 191. -/
theorem bounds_12_191 : exactInterval 12 191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_191 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 191) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_191 : oddCount 191 12 = 8 ∧ acceleratedOrbit 12 191 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_191 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 191) = 3 ^ 8 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_191.1, data_12_191.2]

/-- Complete interval computation for depth 12, residue 192. -/
theorem bounds_12_192 : exactInterval 12 192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_192 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 192) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_192 : oddCount 192 12 = 3 ∧ acceleratedOrbit 12 192 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_192 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 192) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_192.1, data_12_192.2]

/-- Complete interval computation for depth 12, residue 193. -/
theorem bounds_12_193 : exactInterval 12 193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_193 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 193) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_193 : oddCount 193 12 = 7 ∧ acceleratedOrbit 12 193 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_193 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 193) = 3 ^ 7 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_193.1, data_12_193.2]

/-- Complete interval computation for depth 12, residue 194. -/
theorem bounds_12_194 : exactInterval 12 194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_194 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 194) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_194 : oddCount 194 12 = 7 ∧ acceleratedOrbit 12 194 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_194 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 194) = 3 ^ 7 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_194.1, data_12_194.2]

/-- Complete interval computation for depth 12, residue 195. -/
theorem bounds_12_195 : exactInterval 12 195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_195 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 195) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_195 : oddCount 195 12 = 7 ∧ acceleratedOrbit 12 195 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_195 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 195) = 3 ^ 7 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_195.1, data_12_195.2]

/-- Complete interval computation for depth 12, residue 196. -/
theorem bounds_12_196 : exactInterval 12 196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_196 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 196) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_196 : oddCount 196 12 = 5 ∧ acceleratedOrbit 12 196 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_196 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 196) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_196.1, data_12_196.2]

/-- Complete interval computation for depth 12, residue 197. -/
theorem bounds_12_197 : exactInterval 12 197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_197 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 197) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_197 : oddCount 197 12 = 5 ∧ acceleratedOrbit 12 197 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_197 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 197) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_197.1, data_12_197.2]

/-- Complete interval computation for depth 12, residue 198. -/
theorem bounds_12_198 : exactInterval 12 198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_198 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 198) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_198 : oddCount 198 12 = 5 ∧ acceleratedOrbit 12 198 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_198 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 198) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_198.1, data_12_198.2]

end Collatz.Research.StoppingAtlas.Batch0213
