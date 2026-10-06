import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0479

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 174. -/
theorem bounds_13_174 : exactInterval 13 174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_174 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 174) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_174 : oddCount 174 13 = 6 ∧ acceleratedOrbit 13 174 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_174 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 174) = 3 ^ 6 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_174.1, data_13_174.2]

/-- Complete interval computation for depth 13, residue 175. -/
theorem bounds_13_175 : exactInterval 13 175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_175 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 175) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_175 : oddCount 175 13 = 9 ∧ acceleratedOrbit 13 175 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_175 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 175) = 3 ^ 9 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_175.1, data_13_175.2]

/-- Complete interval computation for depth 13, residue 176. -/
theorem bounds_13_176 : exactInterval 13 176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_176 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 176) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_176 : oddCount 176 13 = 4 ∧ acceleratedOrbit 13 176 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_176 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 176) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_176.1, data_13_176.2]

/-- Complete interval computation for depth 13, residue 177. -/
theorem bounds_13_177 : exactInterval 13 177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_177 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 177) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_177 : oddCount 177 13 = 6 ∧ acceleratedOrbit 13 177 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_177 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 177) = 3 ^ 6 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_177.1, data_13_177.2]

/-- Complete interval computation for depth 13, residue 178. -/
theorem bounds_13_178 : exactInterval 13 178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_178 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 178) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_178 : oddCount 178 13 = 6 ∧ acceleratedOrbit 13 178 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_178 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 178) = 3 ^ 6 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_178.1, data_13_178.2]

/-- Complete interval computation for depth 13, residue 179. -/
theorem bounds_13_179 : exactInterval 13 179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_179 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 179) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_179 : oddCount 179 13 = 6 ∧ acceleratedOrbit 13 179 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_179 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 179) = 3 ^ 6 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_179.1, data_13_179.2]

/-- Complete interval computation for depth 13, residue 180. -/
theorem bounds_13_180 : exactInterval 13 180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_180 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 180) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_180 : oddCount 180 13 = 4 ∧ acceleratedOrbit 13 180 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_180 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 180) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_180.1, data_13_180.2]

/-- Complete interval computation for depth 13, residue 181. -/
theorem bounds_13_181 : exactInterval 13 181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_181 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 181) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_181 : oddCount 181 13 = 4 ∧ acceleratedOrbit 13 181 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_181 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 181) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_181.1, data_13_181.2]

/-- Complete interval computation for depth 13, residue 182. -/
theorem bounds_13_182 : exactInterval 13 182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_182 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 182) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_182 : oddCount 182 13 = 9 ∧ acceleratedOrbit 13 182 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_182 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 182) = 3 ^ 9 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_182.1, data_13_182.2]

/-- Complete interval computation for depth 13, residue 183. -/
theorem bounds_13_183 : exactInterval 13 183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_183 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 183) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_183 : oddCount 183 13 = 9 ∧ acceleratedOrbit 13 183 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_183 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 183) = 3 ^ 9 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_183.1, data_13_183.2]

/-- Complete interval computation for depth 13, residue 184. -/
theorem bounds_13_184 : exactInterval 13 184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_184 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 184) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_184 : oddCount 184 13 = 4 ∧ acceleratedOrbit 13 184 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_184 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 184) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_184.1, data_13_184.2]

/-- Complete interval computation for depth 13, residue 185. -/
theorem bounds_13_185 : exactInterval 13 185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_185 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 185) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_185 : oddCount 185 13 = 8 ∧ acceleratedOrbit 13 185 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_185 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 185) = 3 ^ 8 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_185.1, data_13_185.2]

/-- Complete interval computation for depth 13, residue 186. -/
theorem bounds_13_186 : exactInterval 13 186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_186 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 186) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_186 : oddCount 186 13 = 4 ∧ acceleratedOrbit 13 186 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_186 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 186) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_186.1, data_13_186.2]

/-- Complete interval computation for depth 13, residue 187. -/
theorem bounds_13_187 : exactInterval 13 187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_187 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 187) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_187 : oddCount 187 13 = 8 ∧ acceleratedOrbit 13 187 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_187 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 187) = 3 ^ 8 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_187.1, data_13_187.2]

/-- Complete interval computation for depth 13, residue 188. -/
theorem bounds_13_188 : exactInterval 13 188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_188 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 188) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_188 : oddCount 188 13 = 8 ∧ acceleratedOrbit 13 188 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_188 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 188) = 3 ^ 8 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_188.1, data_13_188.2]

end Collatz.Research.StoppingAtlas.Batch0479
