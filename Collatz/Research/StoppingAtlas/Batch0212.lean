import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0212

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 168. -/
theorem bounds_12_168 : exactInterval 12 168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_168 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 168) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_168 : oddCount 168 12 = 3 ∧ acceleratedOrbit 12 168 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_168 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 168) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_168.1, data_12_168.2]

/-- Complete interval computation for depth 12, residue 169. -/
theorem bounds_12_169 : exactInterval 12 169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_169 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 169) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_169 : oddCount 169 12 = 9 ∧ acceleratedOrbit 12 169 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_169 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 169) = 3 ^ 9 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_169.1, data_12_169.2]

/-- Complete interval computation for depth 12, residue 170. -/
theorem bounds_12_170 : exactInterval 12 170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_170 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 170) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_170 : oddCount 170 12 = 3 ∧ acceleratedOrbit 12 170 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_170 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 170) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_170.1, data_12_170.2]

/-- Complete interval computation for depth 12, residue 171. -/
theorem bounds_12_171 : exactInterval 12 171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_171 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 171) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_171 : oddCount 171 12 = 6 ∧ acceleratedOrbit 12 171 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_171 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 171) = 3 ^ 6 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_171.1, data_12_171.2]

/-- Complete interval computation for depth 12, residue 172. -/
theorem bounds_12_172 : exactInterval 12 172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_172 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 172) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_172 : oddCount 172 12 = 5 ∧ acceleratedOrbit 12 172 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_172 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 172) = 3 ^ 5 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_172.1, data_12_172.2]

/-- Complete interval computation for depth 12, residue 173. -/
theorem bounds_12_173 : exactInterval 12 173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_173 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 173) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_173 : oddCount 173 12 = 5 ∧ acceleratedOrbit 12 173 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_173 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 173) = 3 ^ 5 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_173.1, data_12_173.2]

/-- Complete interval computation for depth 12, residue 174. -/
theorem bounds_12_174 : exactInterval 12 174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_174 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 174) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_174 : oddCount 174 12 = 5 ∧ acceleratedOrbit 12 174 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_174 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 174) = 3 ^ 5 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_174.1, data_12_174.2]

/-- Complete interval computation for depth 12, residue 175. -/
theorem bounds_12_175 : exactInterval 12 175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_175 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 175) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_175 : oddCount 175 12 = 8 ∧ acceleratedOrbit 12 175 = 283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_175 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 175) = 3 ^ 8 * m + 283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_175.1, data_12_175.2]

/-- Complete interval computation for depth 12, residue 176. -/
theorem bounds_12_176 : exactInterval 12 176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_176 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 176) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_176 : oddCount 176 12 = 4 ∧ acceleratedOrbit 12 176 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_176 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 176) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_176.1, data_12_176.2]

/-- Complete interval computation for depth 12, residue 177. -/
theorem bounds_12_177 : exactInterval 12 177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_177 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 177) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_177 : oddCount 177 12 = 5 ∧ acceleratedOrbit 12 177 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_177 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 177) = 3 ^ 5 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_177.1, data_12_177.2]

/-- Complete interval computation for depth 12, residue 178. -/
theorem bounds_12_178 : exactInterval 12 178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_178 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 178) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_178 : oddCount 178 12 = 5 ∧ acceleratedOrbit 12 178 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_178 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 178) = 3 ^ 5 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_178.1, data_12_178.2]

/-- Complete interval computation for depth 12, residue 179. -/
theorem bounds_12_179 : exactInterval 12 179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_179 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 179) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_179 : oddCount 179 12 = 5 ∧ acceleratedOrbit 12 179 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_179 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 179) = 3 ^ 5 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_179.1, data_12_179.2]

/-- Complete interval computation for depth 12, residue 180. -/
theorem bounds_12_180 : exactInterval 12 180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_180 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 180) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_180 : oddCount 180 12 = 4 ∧ acceleratedOrbit 12 180 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_180 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 180) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_180.1, data_12_180.2]

/-- Complete interval computation for depth 12, residue 181. -/
theorem bounds_12_181 : exactInterval 12 181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_181 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 181) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_181 : oddCount 181 12 = 4 ∧ acceleratedOrbit 12 181 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_181 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 181) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_181.1, data_12_181.2]

/-- Complete interval computation for depth 12, residue 182. -/
theorem bounds_12_182 : exactInterval 12 182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_182 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 182) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_182 : oddCount 182 12 = 9 ∧ acceleratedOrbit 12 182 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_182 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 182) = 3 ^ 9 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_182.1, data_12_182.2]

/-- Complete interval computation for depth 12, residue 183. -/
theorem bounds_12_183 : exactInterval 12 183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_183 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 183) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_183 : oddCount 183 12 = 9 ∧ acceleratedOrbit 12 183 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_183 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 183) = 3 ^ 9 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_183.1, data_12_183.2]

end Collatz.Research.StoppingAtlas.Batch0212
