import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0012

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 168. -/
theorem bounds_10_168 : exactInterval 10 168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_168 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 168) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_168 : oddCount 168 10 = 2 ∧ acceleratedOrbit 10 168 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_168 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 168) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_168.1, data_10_168.2]

/-- Complete interval computation for depth 10, residue 169. -/
theorem bounds_10_169 : exactInterval 10 169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_169 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 169) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_169 : oddCount 169 10 = 8 ∧ acceleratedOrbit 10 169 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_169 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 169) = 3 ^ 8 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_169.1, data_10_169.2]

/-- Complete interval computation for depth 10, residue 170. -/
theorem bounds_10_170 : exactInterval 10 170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_170 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 170) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_170 : oddCount 170 10 = 2 ∧ acceleratedOrbit 10 170 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_170 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 170) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_170.1, data_10_170.2]

/-- Complete interval computation for depth 10, residue 171. -/
theorem bounds_10_171 : exactInterval 10 171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_171 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 171) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_171 : oddCount 171 10 = 5 ∧ acceleratedOrbit 10 171 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_171 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 171) = 3 ^ 5 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_171.1, data_10_171.2]

/-- Complete interval computation for depth 10, residue 172. -/
theorem bounds_10_172 : exactInterval 10 172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_172 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 172) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_172 : oddCount 172 10 = 4 ∧ acceleratedOrbit 10 172 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_172 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 172) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_172.1, data_10_172.2]

/-- Complete interval computation for depth 10, residue 173. -/
theorem bounds_10_173 : exactInterval 10 173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_173 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 173) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_173 : oddCount 173 10 = 4 ∧ acceleratedOrbit 10 173 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_173 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 173) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_173.1, data_10_173.2]

/-- Complete interval computation for depth 10, residue 174. -/
theorem bounds_10_174 : exactInterval 10 174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_174 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 174) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_174 : oddCount 174 10 = 4 ∧ acceleratedOrbit 10 174 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_174 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 174) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_174.1, data_10_174.2]

/-- Complete interval computation for depth 10, residue 175. -/
theorem bounds_10_175 : exactInterval 10 175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_175 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 175) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_175 : oddCount 175 10 = 7 ∧ acceleratedOrbit 10 175 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_175 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 175) = 3 ^ 7 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_175.1, data_10_175.2]

/-- Complete interval computation for depth 10, residue 176. -/
theorem bounds_10_176 : exactInterval 10 176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_176 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 176) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_176 : oddCount 176 10 = 3 ∧ acceleratedOrbit 10 176 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_176 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 176) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_176.1, data_10_176.2]

/-- Complete interval computation for depth 10, residue 177. -/
theorem bounds_10_177 : exactInterval 10 177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_177 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 177) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_177 : oddCount 177 10 = 5 ∧ acceleratedOrbit 10 177 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_177 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 177) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_177.1, data_10_177.2]

/-- Complete interval computation for depth 10, residue 178. -/
theorem bounds_10_178 : exactInterval 10 178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_178 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 178) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_178 : oddCount 178 10 = 5 ∧ acceleratedOrbit 10 178 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_178 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 178) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_178.1, data_10_178.2]

/-- Complete interval computation for depth 10, residue 179. -/
theorem bounds_10_179 : exactInterval 10 179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_179 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 179) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_179 : oddCount 179 10 = 5 ∧ acceleratedOrbit 10 179 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_179 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 179) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_179.1, data_10_179.2]

/-- Complete interval computation for depth 10, residue 180. -/
theorem bounds_10_180 : exactInterval 10 180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_180 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 180) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_180 : oddCount 180 10 = 3 ∧ acceleratedOrbit 10 180 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_180 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 180) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_180.1, data_10_180.2]

/-- Complete interval computation for depth 10, residue 181. -/
theorem bounds_10_181 : exactInterval 10 181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_181 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 181) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_181 : oddCount 181 10 = 3 ∧ acceleratedOrbit 10 181 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_181 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 181) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_181.1, data_10_181.2]

/-- Complete interval computation for depth 10, residue 182. -/
theorem bounds_10_182 : exactInterval 10 182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_182 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 182) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_182 : oddCount 182 10 = 7 ∧ acceleratedOrbit 10 182 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_182 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 182) = 3 ^ 7 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_182.1, data_10_182.2]

/-- Complete interval computation for depth 10, residue 183. -/
theorem bounds_10_183 : exactInterval 10 183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_183 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 183) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_183 : oddCount 183 10 = 7 ∧ acceleratedOrbit 10 183 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_183 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 183) = 3 ^ 7 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_183.1, data_10_183.2]

end Collatz.Research.StoppingAtlas.Batch0012
