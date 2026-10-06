import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0080

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 189. -/
theorem bounds_11_189 : exactInterval 11 189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_189 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 189) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_189 : oddCount 189 11 = 7 ∧ acceleratedOrbit 11 189 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_189 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 189) = 3 ^ 7 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_189.1, data_11_189.2]

/-- Complete interval computation for depth 11, residue 190. -/
theorem bounds_11_190 : exactInterval 11 190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_190 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 190) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_190 : oddCount 190 11 = 7 ∧ acceleratedOrbit 11 190 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_190 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 190) = 3 ^ 7 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_190.1, data_11_190.2]

/-- Complete interval computation for depth 11, residue 191. -/
theorem bounds_11_191 : exactInterval 11 191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_191 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 191) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_191 : oddCount 191 11 = 7 ∧ acceleratedOrbit 11 191 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_191 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 191) = 3 ^ 7 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_191.1, data_11_191.2]

/-- Complete interval computation for depth 11, residue 192. -/
theorem bounds_11_192 : exactInterval 11 192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_192 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 192) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_192 : oddCount 192 11 = 2 ∧ acceleratedOrbit 11 192 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_192 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 192) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_192.1, data_11_192.2]

/-- Complete interval computation for depth 11, residue 193. -/
theorem bounds_11_193 : exactInterval 11 193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_193 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 193) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_193 : oddCount 193 11 = 6 ∧ acceleratedOrbit 11 193 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_193 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 193) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_193.1, data_11_193.2]

/-- Complete interval computation for depth 11, residue 194. -/
theorem bounds_11_194 : exactInterval 11 194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_194 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 194) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_194 : oddCount 194 11 = 6 ∧ acceleratedOrbit 11 194 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_194 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 194) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_194.1, data_11_194.2]

/-- Complete interval computation for depth 11, residue 195. -/
theorem bounds_11_195 : exactInterval 11 195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_195 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 195) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_195 : oddCount 195 11 = 6 ∧ acceleratedOrbit 11 195 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_195 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 195) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_195.1, data_11_195.2]

/-- Complete interval computation for depth 11, residue 196. -/
theorem bounds_11_196 : exactInterval 11 196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_196 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 196) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_196 : oddCount 196 11 = 5 ∧ acceleratedOrbit 11 196 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_196 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 196) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_196.1, data_11_196.2]

/-- Complete interval computation for depth 11, residue 197. -/
theorem bounds_11_197 : exactInterval 11 197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_197 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 197) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_197 : oddCount 197 11 = 5 ∧ acceleratedOrbit 11 197 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_197 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 197) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_197.1, data_11_197.2]

/-- Complete interval computation for depth 11, residue 198. -/
theorem bounds_11_198 : exactInterval 11 198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_198 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 198) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_198 : oddCount 198 11 = 5 ∧ acceleratedOrbit 11 198 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_198 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 198) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_198.1, data_11_198.2]

/-- Complete interval computation for depth 11, residue 199. -/
theorem bounds_11_199 : exactInterval 11 199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_199 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 199) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_199 : oddCount 199 11 = 7 ∧ acceleratedOrbit 11 199 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_199 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 199) = 3 ^ 7 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_199.1, data_11_199.2]

/-- Complete interval computation for depth 11, residue 200. -/
theorem bounds_11_200 : exactInterval 11 200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_200 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 200) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_200 : oddCount 200 11 = 5 ∧ acceleratedOrbit 11 200 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_200 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 200) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_200.1, data_11_200.2]

/-- Complete interval computation for depth 11, residue 201. -/
theorem bounds_11_201 : exactInterval 11 201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_201 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 201) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_201 : oddCount 201 11 = 4 ∧ acceleratedOrbit 11 201 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_201 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 201) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_201.1, data_11_201.2]

/-- Complete interval computation for depth 11, residue 202. -/
theorem bounds_11_202 : exactInterval 11 202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_202 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 202) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_202 : oddCount 202 11 = 5 ∧ acceleratedOrbit 11 202 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_202 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 202) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_202.1, data_11_202.2]

/-- Complete interval computation for depth 11, residue 203. -/
theorem bounds_11_203 : exactInterval 11 203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_203 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 203) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_203 : oddCount 203 11 = 6 ∧ acceleratedOrbit 11 203 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_203 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 203) = 3 ^ 6 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_203.1, data_11_203.2]

end Collatz.Research.StoppingAtlas.Batch0080
