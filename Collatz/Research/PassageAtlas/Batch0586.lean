import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0586

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 19169. -/
theorem bounds_15_19169 : exactInterval 15 19169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19169 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19169) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19169 : oddCount 19169 15 = 9 ∧ acceleratedOrbit 15 19169 = 11516 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19169 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19169) = 3 ^ 9 * m + 11516 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19169.1, data_15_19169.2]

/-- Complete interval computation for depth 15, residue 19170. -/
theorem bounds_15_19170 : exactInterval 15 19170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19170 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19170) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19170 : oddCount 19170 15 = 5 ∧ acceleratedOrbit 15 19170 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19170 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19170) = 3 ^ 5 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19170.1, data_15_19170.2]

/-- Complete interval computation for depth 15, residue 19171. -/
theorem bounds_15_19171 : exactInterval 15 19171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19171 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19171) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19171 : oddCount 19171 15 = 5 ∧ acceleratedOrbit 15 19171 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19171 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19171) = 3 ^ 5 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19171.1, data_15_19171.2]

/-- Complete interval computation for depth 15, residue 19172. -/
theorem bounds_15_19172 : exactInterval 15 19172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19172 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19172) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19172 : oddCount 19172 15 = 6 ∧ acceleratedOrbit 15 19172 = 427 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19172 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19172) = 3 ^ 6 * m + 427 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19172.1, data_15_19172.2]

/-- Complete interval computation for depth 15, residue 19173. -/
theorem bounds_15_19173 : exactInterval 15 19173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19173 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19173) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19173 : oddCount 19173 15 = 6 ∧ acceleratedOrbit 15 19173 = 427 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19173 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19173) = 3 ^ 6 * m + 427 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19173.1, data_15_19173.2]

/-- Complete interval computation for depth 15, residue 19174. -/
theorem bounds_15_19174 : exactInterval 15 19174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19174 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19174) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19174 : oddCount 19174 15 = 6 ∧ acceleratedOrbit 15 19174 = 427 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19174 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19174) = 3 ^ 6 * m + 427 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19174.1, data_15_19174.2]

/-- Complete interval computation for depth 15, residue 19175. -/
theorem bounds_15_19175 : exactInterval 15 19175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19175 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19175) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19175 : oddCount 19175 15 = 11 ∧ acceleratedOrbit 15 19175 = 103670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19175 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19175) = 3 ^ 11 * m + 103670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19175.1, data_15_19175.2]

/-- Complete interval computation for depth 15, residue 19176. -/
theorem bounds_15_19176 : exactInterval 15 19176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19176 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19176) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19176 : oddCount 19176 15 = 5 ∧ acceleratedOrbit 15 19176 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19176 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19176) = 3 ^ 5 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19176.1, data_15_19176.2]

/-- Complete interval computation for depth 15, residue 19177. -/
theorem bounds_15_19177 : exactInterval 15 19177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19177 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19177) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19177 : oddCount 19177 15 = 10 ∧ acceleratedOrbit 15 19177 = 34562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19177 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19177) = 3 ^ 10 * m + 34562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19177.1, data_15_19177.2]

/-- Complete interval computation for depth 15, residue 19178. -/
theorem bounds_15_19178 : exactInterval 15 19178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19178 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19178) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19178 : oddCount 19178 15 = 5 ∧ acceleratedOrbit 15 19178 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19178 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19178) = 3 ^ 5 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19178.1, data_15_19178.2]

/-- Complete interval computation for depth 15, residue 19179. -/
theorem bounds_15_19179 : exactInterval 15 19179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19179 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19179) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19179 : oddCount 19179 15 = 9 ∧ acceleratedOrbit 15 19179 = 11522 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19179 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19179) = 3 ^ 9 * m + 11522 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19179.1, data_15_19179.2]

/-- Complete interval computation for depth 15, residue 19180. -/
theorem bounds_15_19180 : exactInterval 15 19180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19180 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19180) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19180 : oddCount 19180 15 = 9 ∧ acceleratedOrbit 15 19180 = 11528 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19180 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19180) = 3 ^ 9 * m + 11528 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19180.1, data_15_19180.2]

/-- Complete interval computation for depth 15, residue 19181. -/
theorem bounds_15_19181 : exactInterval 15 19181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19181 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19181) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19181 : oddCount 19181 15 = 9 ∧ acceleratedOrbit 15 19181 = 11528 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19181 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19181) = 3 ^ 9 * m + 11528 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19181.1, data_15_19181.2]

/-- Complete interval computation for depth 15, residue 19182. -/
theorem bounds_15_19182 : exactInterval 15 19182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19182 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19182) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19182 : oddCount 19182 15 = 9 ∧ acceleratedOrbit 15 19182 = 11528 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19182 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19182) = 3 ^ 9 * m + 11528 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19182.1, data_15_19182.2]

/-- Complete interval computation for depth 15, residue 19183. -/
theorem bounds_15_19183 : exactInterval 15 19183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19183 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19183) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19183 : oddCount 19183 15 = 10 ∧ acceleratedOrbit 15 19183 = 34571 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19183 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19183) = 3 ^ 10 * m + 34571 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19183.1, data_15_19183.2]

/-- Complete interval computation for depth 15, residue 19184. -/
theorem bounds_15_19184 : exactInterval 15 19184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19184 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19184) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19184 : oddCount 19184 15 = 7 ∧ acceleratedOrbit 15 19184 = 1282 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19184 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19184) = 3 ^ 7 * m + 1282 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19184.1, data_15_19184.2]

/-- Complete interval computation for depth 15, residue 19185. -/
theorem bounds_15_19185 : exactInterval 15 19185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19185 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19185) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19185 : oddCount 19185 15 = 5 ∧ acceleratedOrbit 15 19185 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19185 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19185) = 3 ^ 5 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19185.1, data_15_19185.2]

/-- Complete interval computation for depth 15, residue 19186. -/
theorem bounds_15_19186 : exactInterval 15 19186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19186 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19186) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19186 : oddCount 19186 15 = 10 ∧ acceleratedOrbit 15 19186 = 34582 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19186 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19186) = 3 ^ 10 * m + 34582 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19186.1, data_15_19186.2]

/-- Complete interval computation for depth 15, residue 19187. -/
theorem bounds_15_19187 : exactInterval 15 19187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19187 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19187) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19187 : oddCount 19187 15 = 10 ∧ acceleratedOrbit 15 19187 = 34582 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19187 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19187) = 3 ^ 10 * m + 34582 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19187.1, data_15_19187.2]

/-- Complete interval computation for depth 15, residue 19188. -/
theorem bounds_15_19188 : exactInterval 15 19188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19188 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19188) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19188 : oddCount 19188 15 = 7 ∧ acceleratedOrbit 15 19188 = 1282 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19188 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19188) = 3 ^ 7 * m + 1282 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19188.1, data_15_19188.2]

/-- Complete interval computation for depth 15, residue 19189. -/
theorem bounds_15_19189 : exactInterval 15 19189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19189 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19189) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19189 : oddCount 19189 15 = 7 ∧ acceleratedOrbit 15 19189 = 1282 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19189 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19189) = 3 ^ 7 * m + 1282 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19189.1, data_15_19189.2]

/-- Complete interval computation for depth 15, residue 19190. -/
theorem bounds_15_19190 : exactInterval 15 19190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19190 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19190) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19190 : oddCount 19190 15 = 6 ∧ acceleratedOrbit 15 19190 = 427 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19190 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19190) = 3 ^ 6 * m + 427 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19190.1, data_15_19190.2]

/-- Complete interval computation for depth 15, residue 19191. -/
theorem bounds_15_19191 : exactInterval 15 19191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19191 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19191) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19191 : oddCount 19191 15 = 6 ∧ acceleratedOrbit 15 19191 = 427 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19191 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19191) = 3 ^ 6 * m + 427 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19191.1, data_15_19191.2]

/-- Complete interval computation for depth 15, residue 19192. -/
theorem bounds_15_19192 : exactInterval 15 19192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19192 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19192) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19192 : oddCount 19192 15 = 7 ∧ acceleratedOrbit 15 19192 = 1282 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19192 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19192) = 3 ^ 7 * m + 1282 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19192.1, data_15_19192.2]

/-- Complete interval computation for depth 15, residue 19193. -/
theorem bounds_15_19193 : exactInterval 15 19193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19193 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19193) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19193 : oddCount 19193 15 = 8 ∧ acceleratedOrbit 15 19193 = 3844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19193 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19193) = 3 ^ 8 * m + 3844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19193.1, data_15_19193.2]

/-- Complete interval computation for depth 15, residue 19194. -/
theorem bounds_15_19194 : exactInterval 15 19194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19194 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19194) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19194 : oddCount 19194 15 = 7 ∧ acceleratedOrbit 15 19194 = 1282 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19194 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19194) = 3 ^ 7 * m + 1282 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19194.1, data_15_19194.2]

/-- Complete interval computation for depth 15, residue 19195. -/
theorem bounds_15_19195 : exactInterval 15 19195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19195 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19195) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19195 : oddCount 19195 15 = 11 ∧ acceleratedOrbit 15 19195 = 103781 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19195 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19195) = 3 ^ 11 * m + 103781 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19195.1, data_15_19195.2]

/-- Complete interval computation for depth 15, residue 19196. -/
theorem bounds_15_19196 : exactInterval 15 19196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19196 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19196) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19196 : oddCount 19196 15 = 10 ∧ acceleratedOrbit 15 19196 = 34600 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19196 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19196) = 3 ^ 10 * m + 34600 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19196.1, data_15_19196.2]

/-- Complete interval computation for depth 15, residue 19197. -/
theorem bounds_15_19197 : exactInterval 15 19197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19197 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19197) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19197 : oddCount 19197 15 = 10 ∧ acceleratedOrbit 15 19197 = 34600 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19197 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19197) = 3 ^ 10 * m + 34600 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19197.1, data_15_19197.2]

/-- Complete interval computation for depth 15, residue 19198. -/
theorem bounds_15_19198 : exactInterval 15 19198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19198 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19198) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19198 : oddCount 19198 15 = 10 ∧ acceleratedOrbit 15 19198 = 34600 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19198 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19198) = 3 ^ 10 * m + 34600 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19198.1, data_15_19198.2]

/-- Complete interval computation for depth 15, residue 19199. -/
theorem bounds_15_19199 : exactInterval 15 19199 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19199 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19199) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19199 : oddCount 19199 15 = 9 ∧ acceleratedOrbit 15 19199 = 11533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19199 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19199) = 3 ^ 9 * m + 11533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19199.1, data_15_19199.2]

/-- Complete interval computation for depth 15, residue 19200. -/
theorem bounds_15_19200 : exactInterval 15 19200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19200 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19200) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19200 : oddCount 19200 15 = 3 ∧ acceleratedOrbit 15 19200 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19200 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19200) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19200.1, data_15_19200.2]

/-- Complete interval computation for depth 15, residue 19201. -/
theorem bounds_15_19201 : exactInterval 15 19201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19201 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19201) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19201 : oddCount 19201 15 = 8 ∧ acceleratedOrbit 15 19201 = 3847 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19201 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19201) = 3 ^ 8 * m + 3847 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19201.1, data_15_19201.2]

end Collatz.Research.PassageAtlas.Batch0586
