import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0079

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 174. -/
theorem bounds_11_174 : exactInterval 11 174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_174 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 174) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_174 : oddCount 174 11 = 4 ∧ acceleratedOrbit 11 174 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_174 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 174) = 3 ^ 4 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_174.1, data_11_174.2]

/-- Complete interval computation for depth 11, residue 175. -/
theorem bounds_11_175 : exactInterval 11 175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_175 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 175) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_175 : oddCount 175 11 = 8 ∧ acceleratedOrbit 11 175 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_175 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 175) = 3 ^ 8 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_175.1, data_11_175.2]

/-- Complete interval computation for depth 11, residue 176. -/
theorem bounds_11_176 : exactInterval 11 176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_176 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 176) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_176 : oddCount 176 11 = 4 ∧ acceleratedOrbit 11 176 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_176 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 176) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_176.1, data_11_176.2]

/-- Complete interval computation for depth 11, residue 177. -/
theorem bounds_11_177 : exactInterval 11 177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_177 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 177) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_177 : oddCount 177 11 = 5 ∧ acceleratedOrbit 11 177 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_177 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 177) = 3 ^ 5 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_177.1, data_11_177.2]

/-- Complete interval computation for depth 11, residue 178. -/
theorem bounds_11_178 : exactInterval 11 178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_178 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 178) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_178 : oddCount 178 11 = 5 ∧ acceleratedOrbit 11 178 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_178 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 178) = 3 ^ 5 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_178.1, data_11_178.2]

/-- Complete interval computation for depth 11, residue 179. -/
theorem bounds_11_179 : exactInterval 11 179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_179 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 179) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_179 : oddCount 179 11 = 5 ∧ acceleratedOrbit 11 179 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_179 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 179) = 3 ^ 5 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_179.1, data_11_179.2]

/-- Complete interval computation for depth 11, residue 180. -/
theorem bounds_11_180 : exactInterval 11 180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_180 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 180) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_180 : oddCount 180 11 = 4 ∧ acceleratedOrbit 11 180 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_180 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 180) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_180.1, data_11_180.2]

/-- Complete interval computation for depth 11, residue 181. -/
theorem bounds_11_181 : exactInterval 11 181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_181 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 181) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_181 : oddCount 181 11 = 4 ∧ acceleratedOrbit 11 181 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_181 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 181) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_181.1, data_11_181.2]

/-- Complete interval computation for depth 11, residue 182. -/
theorem bounds_11_182 : exactInterval 11 182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_182 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 182) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_182 : oddCount 182 11 = 8 ∧ acceleratedOrbit 11 182 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_182 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 182) = 3 ^ 8 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_182.1, data_11_182.2]

/-- Complete interval computation for depth 11, residue 183. -/
theorem bounds_11_183 : exactInterval 11 183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_183 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 183) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_183 : oddCount 183 11 = 8 ∧ acceleratedOrbit 11 183 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_183 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 183) = 3 ^ 8 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_183.1, data_11_183.2]

/-- Complete interval computation for depth 11, residue 184. -/
theorem bounds_11_184 : exactInterval 11 184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_184 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 184) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_184 : oddCount 184 11 = 4 ∧ acceleratedOrbit 11 184 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_184 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 184) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_184.1, data_11_184.2]

/-- Complete interval computation for depth 11, residue 185. -/
theorem bounds_11_185 : exactInterval 11 185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_185 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 185) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_185 : oddCount 185 11 = 6 ∧ acceleratedOrbit 11 185 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_185 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 185) = 3 ^ 6 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_185.1, data_11_185.2]

/-- Complete interval computation for depth 11, residue 186. -/
theorem bounds_11_186 : exactInterval 11 186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_186 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 186) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_186 : oddCount 186 11 = 4 ∧ acceleratedOrbit 11 186 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_186 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 186) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_186.1, data_11_186.2]

/-- Complete interval computation for depth 11, residue 187. -/
theorem bounds_11_187 : exactInterval 11 187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_187 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 187) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_187 : oddCount 187 11 = 7 ∧ acceleratedOrbit 11 187 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_187 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 187) = 3 ^ 7 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_187.1, data_11_187.2]

/-- Complete interval computation for depth 11, residue 188. -/
theorem bounds_11_188 : exactInterval 11 188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_188 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 188) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_188 : oddCount 188 11 = 7 ∧ acceleratedOrbit 11 188 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_188 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 188) = 3 ^ 7 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_188.1, data_11_188.2]

end Collatz.Research.StoppingAtlas.Batch0079
