import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0480

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 189. -/
theorem bounds_13_189 : exactInterval 13 189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_189 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 189) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_189 : oddCount 189 13 = 8 ∧ acceleratedOrbit 13 189 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_189 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 189) = 3 ^ 8 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_189.1, data_13_189.2]

/-- Complete interval computation for depth 13, residue 190. -/
theorem bounds_13_190 : exactInterval 13 190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_190 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 190) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_190 : oddCount 190 13 = 8 ∧ acceleratedOrbit 13 190 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_190 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 190) = 3 ^ 8 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_190.1, data_13_190.2]

/-- Complete interval computation for depth 13, residue 191. -/
theorem bounds_13_191 : exactInterval 13 191 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_191 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 191) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_191 : oddCount 191 13 = 8 ∧ acceleratedOrbit 13 191 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_191 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 191) = 3 ^ 8 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_191.1, data_13_191.2]

/-- Complete interval computation for depth 13, residue 192. -/
theorem bounds_13_192 : exactInterval 13 192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_192 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 192) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_192 : oddCount 192 13 = 3 ∧ acceleratedOrbit 13 192 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_192 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 192) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_192.1, data_13_192.2]

/-- Complete interval computation for depth 13, residue 193. -/
theorem bounds_13_193 : exactInterval 13 193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_193 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 193) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_193 : oddCount 193 13 = 8 ∧ acceleratedOrbit 13 193 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_193 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 193) = 3 ^ 8 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_193.1, data_13_193.2]

/-- Complete interval computation for depth 13, residue 194. -/
theorem bounds_13_194 : exactInterval 13 194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_194 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 194) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_194 : oddCount 194 13 = 8 ∧ acceleratedOrbit 13 194 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_194 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 194) = 3 ^ 8 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_194.1, data_13_194.2]

/-- Complete interval computation for depth 13, residue 195. -/
theorem bounds_13_195 : exactInterval 13 195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_195 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 195) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_195 : oddCount 195 13 = 8 ∧ acceleratedOrbit 13 195 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_195 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 195) = 3 ^ 8 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_195.1, data_13_195.2]

/-- Complete interval computation for depth 13, residue 196. -/
theorem bounds_13_196 : exactInterval 13 196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_196 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 196) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_196 : oddCount 196 13 = 6 ∧ acceleratedOrbit 13 196 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_196 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 196) = 3 ^ 6 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_196.1, data_13_196.2]

/-- Complete interval computation for depth 13, residue 197. -/
theorem bounds_13_197 : exactInterval 13 197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_197 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 197) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_197 : oddCount 197 13 = 6 ∧ acceleratedOrbit 13 197 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_197 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 197) = 3 ^ 6 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_197.1, data_13_197.2]

/-- Complete interval computation for depth 13, residue 198. -/
theorem bounds_13_198 : exactInterval 13 198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_198 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 198) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_198 : oddCount 198 13 = 6 ∧ acceleratedOrbit 13 198 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_198 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 198) = 3 ^ 6 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_198.1, data_13_198.2]

/-- Complete interval computation for depth 13, residue 199. -/
theorem bounds_13_199 : exactInterval 13 199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_199 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 199) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_199 : oddCount 199 13 = 9 ∧ acceleratedOrbit 13 199 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_199 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 199) = 3 ^ 9 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_199.1, data_13_199.2]

/-- Complete interval computation for depth 13, residue 200. -/
theorem bounds_13_200 : exactInterval 13 200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_200 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 200) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_200 : oddCount 200 13 = 6 ∧ acceleratedOrbit 13 200 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_200 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 200) = 3 ^ 6 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_200.1, data_13_200.2]

/-- Complete interval computation for depth 13, residue 201. -/
theorem bounds_13_201 : exactInterval 13 201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_201 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 201) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_201 : oddCount 201 13 = 4 ∧ acceleratedOrbit 13 201 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_201 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 201) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_201.1, data_13_201.2]

/-- Complete interval computation for depth 13, residue 202. -/
theorem bounds_13_202 : exactInterval 13 202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_202 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 202) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_202 : oddCount 202 13 = 6 ∧ acceleratedOrbit 13 202 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_202 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 202) = 3 ^ 6 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_202.1, data_13_202.2]

/-- Complete interval computation for depth 13, residue 203. -/
theorem bounds_13_203 : exactInterval 13 203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_203 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 203) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_203 : oddCount 203 13 = 7 ∧ acceleratedOrbit 13 203 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_203 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 203) = 3 ^ 7 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_203.1, data_13_203.2]

end Collatz.Research.StoppingAtlas.Batch0480
