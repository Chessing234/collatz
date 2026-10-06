import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0013

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 184. -/
theorem bounds_10_184 : exactInterval 10 184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_184 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 184) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_184 : oddCount 184 10 = 3 ∧ acceleratedOrbit 10 184 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_184 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 184) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_184.1, data_10_184.2]

/-- Complete interval computation for depth 10, residue 185. -/
theorem bounds_10_185 : exactInterval 10 185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_185 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 185) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_185 : oddCount 185 10 = 6 ∧ acceleratedOrbit 10 185 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_185 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 185) = 3 ^ 6 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_185.1, data_10_185.2]

/-- Complete interval computation for depth 10, residue 186. -/
theorem bounds_10_186 : exactInterval 10 186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_186 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 186) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_186 : oddCount 186 10 = 3 ∧ acceleratedOrbit 10 186 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_186 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 186) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_186.1, data_10_186.2]

/-- Complete interval computation for depth 10, residue 187. -/
theorem bounds_10_187 : exactInterval 10 187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_187 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 187) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_187 : oddCount 187 10 = 7 ∧ acceleratedOrbit 10 187 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_187 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 187) = 3 ^ 7 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_187.1, data_10_187.2]

/-- Complete interval computation for depth 10, residue 188. -/
theorem bounds_10_188 : exactInterval 10 188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_188 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 188) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_188 : oddCount 188 10 = 6 ∧ acceleratedOrbit 10 188 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_188 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 188) = 3 ^ 6 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_188.1, data_10_188.2]

/-- Complete interval computation for depth 10, residue 189. -/
theorem bounds_10_189 : exactInterval 10 189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_189 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 189) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_189 : oddCount 189 10 = 6 ∧ acceleratedOrbit 10 189 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_189 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 189) = 3 ^ 6 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_189.1, data_10_189.2]

/-- Complete interval computation for depth 10, residue 190. -/
theorem bounds_10_190 : exactInterval 10 190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_190 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 190) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_190 : oddCount 190 10 = 6 ∧ acceleratedOrbit 10 190 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_190 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 190) = 3 ^ 6 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_190.1, data_10_190.2]

/-- Complete interval computation for depth 10, residue 191. -/
theorem bounds_10_191 : exactInterval 10 191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_191 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 191) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_191 : oddCount 191 10 = 7 ∧ acceleratedOrbit 10 191 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_191 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 191) = 3 ^ 7 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_191.1, data_10_191.2]

/-- Complete interval computation for depth 10, residue 192. -/
theorem bounds_10_192 : exactInterval 10 192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_192 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 192) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_192 : oddCount 192 10 = 2 ∧ acceleratedOrbit 10 192 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_192 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 192) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_192.1, data_10_192.2]

/-- Complete interval computation for depth 10, residue 193. -/
theorem bounds_10_193 : exactInterval 10 193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_193 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 193) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_193 : oddCount 193 10 = 5 ∧ acceleratedOrbit 10 193 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_193 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 193) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_193.1, data_10_193.2]

/-- Complete interval computation for depth 10, residue 194. -/
theorem bounds_10_194 : exactInterval 10 194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_194 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 194) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_194 : oddCount 194 10 = 5 ∧ acceleratedOrbit 10 194 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_194 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 194) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_194.1, data_10_194.2]

/-- Complete interval computation for depth 10, residue 195. -/
theorem bounds_10_195 : exactInterval 10 195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_195 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 195) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_195 : oddCount 195 10 = 5 ∧ acceleratedOrbit 10 195 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_195 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 195) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_195.1, data_10_195.2]

/-- Complete interval computation for depth 10, residue 196. -/
theorem bounds_10_196 : exactInterval 10 196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_196 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 196) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_196 : oddCount 196 10 = 4 ∧ acceleratedOrbit 10 196 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_196 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 196) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_196.1, data_10_196.2]

/-- Complete interval computation for depth 10, residue 197. -/
theorem bounds_10_197 : exactInterval 10 197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_197 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 197) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_197 : oddCount 197 10 = 4 ∧ acceleratedOrbit 10 197 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_197 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 197) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_197.1, data_10_197.2]

/-- Complete interval computation for depth 10, residue 198. -/
theorem bounds_10_198 : exactInterval 10 198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_198 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 198) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_198 : oddCount 198 10 = 4 ∧ acceleratedOrbit 10 198 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_198 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 198) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_198.1, data_10_198.2]

end Collatz.Research.StoppingAtlas.Batch0013
