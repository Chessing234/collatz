import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0647

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 21168. -/
theorem bounds_15_21168 : exactInterval 15 21168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21168 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21168) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21168 : oddCount 21168 15 = 6 ∧ acceleratedOrbit 15 21168 = 472 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21168 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21168) = 3 ^ 6 * m + 472 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21168.1, data_15_21168.2]

/-- Complete interval computation for depth 15, residue 21169. -/
theorem bounds_15_21169 : exactInterval 15 21169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21169 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21169) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21169 : oddCount 21169 15 = 7 ∧ acceleratedOrbit 15 21169 = 1414 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21169 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21169) = 3 ^ 7 * m + 1414 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21169.1, data_15_21169.2]

/-- Complete interval computation for depth 15, residue 21170. -/
theorem bounds_15_21170 : exactInterval 15 21170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21170 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21170) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21170 : oddCount 21170 15 = 7 ∧ acceleratedOrbit 15 21170 = 1414 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21170 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21170) = 3 ^ 7 * m + 1414 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21170.1, data_15_21170.2]

/-- Complete interval computation for depth 15, residue 21171. -/
theorem bounds_15_21171 : exactInterval 15 21171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21171 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21171) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21171 : oddCount 21171 15 = 7 ∧ acceleratedOrbit 15 21171 = 1414 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21171 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21171) = 3 ^ 7 * m + 1414 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21171.1, data_15_21171.2]

/-- Complete interval computation for depth 15, residue 21172. -/
theorem bounds_15_21172 : exactInterval 15 21172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21172 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21172) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21172 : oddCount 21172 15 = 6 ∧ acceleratedOrbit 15 21172 = 472 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21172 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21172) = 3 ^ 6 * m + 472 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21172.1, data_15_21172.2]

/-- Complete interval computation for depth 15, residue 21173. -/
theorem bounds_15_21173 : exactInterval 15 21173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21173 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21173) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21173 : oddCount 21173 15 = 6 ∧ acceleratedOrbit 15 21173 = 472 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21173 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21173) = 3 ^ 6 * m + 472 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21173.1, data_15_21173.2]

/-- Complete interval computation for depth 15, residue 21174. -/
theorem bounds_15_21174 : exactInterval 15 21174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21174 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21174) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21174 : oddCount 21174 15 = 8 ∧ acceleratedOrbit 15 21174 = 4241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21174 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21174) = 3 ^ 8 * m + 4241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21174.1, data_15_21174.2]

/-- Complete interval computation for depth 15, residue 21175. -/
theorem bounds_15_21175 : exactInterval 15 21175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21175 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21175) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21175 : oddCount 21175 15 = 8 ∧ acceleratedOrbit 15 21175 = 4241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21175 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21175) = 3 ^ 8 * m + 4241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21175.1, data_15_21175.2]

/-- Complete interval computation for depth 15, residue 21176. -/
theorem bounds_15_21176 : exactInterval 15 21176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21176 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21176) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21176 : oddCount 21176 15 = 6 ∧ acceleratedOrbit 15 21176 = 472 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21176 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21176) = 3 ^ 6 * m + 472 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21176.1, data_15_21176.2]

/-- Complete interval computation for depth 15, residue 21177. -/
theorem bounds_15_21177 : exactInterval 15 21177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21177 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21177) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21177 : oddCount 21177 15 = 7 ∧ acceleratedOrbit 15 21177 = 1414 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21177 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21177) = 3 ^ 7 * m + 1414 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21177.1, data_15_21177.2]

/-- Complete interval computation for depth 15, residue 21178. -/
theorem bounds_15_21178 : exactInterval 15 21178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21178 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21178) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21178 : oddCount 21178 15 = 6 ∧ acceleratedOrbit 15 21178 = 472 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21178 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21178) = 3 ^ 6 * m + 472 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21178.1, data_15_21178.2]

/-- Complete interval computation for depth 15, residue 21179. -/
theorem bounds_15_21179 : exactInterval 15 21179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21179 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21179) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21179 : oddCount 21179 15 = 10 ∧ acceleratedOrbit 15 21179 = 38171 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21179 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21179) = 3 ^ 10 * m + 38171 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21179.1, data_15_21179.2]

/-- Complete interval computation for depth 15, residue 21180. -/
theorem bounds_15_21180 : exactInterval 15 21180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21180 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21180) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21180 : oddCount 21180 15 = 7 ∧ acceleratedOrbit 15 21180 = 1414 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21180 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21180) = 3 ^ 7 * m + 1414 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21180.1, data_15_21180.2]

/-- Complete interval computation for depth 15, residue 21181. -/
theorem bounds_15_21181 : exactInterval 15 21181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21181 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21181) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21181 : oddCount 21181 15 = 7 ∧ acceleratedOrbit 15 21181 = 1414 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21181 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21181) = 3 ^ 7 * m + 1414 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21181.1, data_15_21181.2]

/-- Complete interval computation for depth 15, residue 21182. -/
theorem bounds_15_21182 : exactInterval 15 21182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21182 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21182) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21182 : oddCount 21182 15 = 7 ∧ acceleratedOrbit 15 21182 = 1414 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21182 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21182) = 3 ^ 7 * m + 1414 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21182.1, data_15_21182.2]

/-- Complete interval computation for depth 15, residue 21183. -/
theorem bounds_15_21183 : exactInterval 15 21183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21183 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21183) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21183 : oddCount 21183 15 = 11 ∧ acceleratedOrbit 15 21183 = 114524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21183 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21183) = 3 ^ 11 * m + 114524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21183.1, data_15_21183.2]

/-- Complete interval computation for depth 15, residue 21184. -/
theorem bounds_15_21184 : exactInterval 15 21184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21184 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21184) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21184 : oddCount 21184 15 = 4 ∧ acceleratedOrbit 15 21184 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21184 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21184) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21184.1, data_15_21184.2]

/-- Complete interval computation for depth 15, residue 21185. -/
theorem bounds_15_21185 : exactInterval 15 21185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21185 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21185) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21185 : oddCount 21185 15 = 6 ∧ acceleratedOrbit 15 21185 = 472 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21185 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21185) = 3 ^ 6 * m + 472 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21185.1, data_15_21185.2]

/-- Complete interval computation for depth 15, residue 21186. -/
theorem bounds_15_21186 : exactInterval 15 21186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21186 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21186) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21186 : oddCount 21186 15 = 9 ∧ acceleratedOrbit 15 21186 = 12730 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21186 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21186) = 3 ^ 9 * m + 12730 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21186.1, data_15_21186.2]

/-- Complete interval computation for depth 15, residue 21187. -/
theorem bounds_15_21187 : exactInterval 15 21187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21187 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21187) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21187 : oddCount 21187 15 = 9 ∧ acceleratedOrbit 15 21187 = 12730 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21187 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21187) = 3 ^ 9 * m + 12730 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21187.1, data_15_21187.2]

/-- Complete interval computation for depth 15, residue 21188. -/
theorem bounds_15_21188 : exactInterval 15 21188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21188 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21188) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21188 : oddCount 21188 15 = 7 ∧ acceleratedOrbit 15 21188 = 1417 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21188 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21188) = 3 ^ 7 * m + 1417 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21188.1, data_15_21188.2]

/-- Complete interval computation for depth 15, residue 21189. -/
theorem bounds_15_21189 : exactInterval 15 21189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21189 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21189) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21189 : oddCount 21189 15 = 7 ∧ acceleratedOrbit 15 21189 = 1417 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21189 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21189) = 3 ^ 7 * m + 1417 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21189.1, data_15_21189.2]

/-- Complete interval computation for depth 15, residue 21190. -/
theorem bounds_15_21190 : exactInterval 15 21190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21190 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21190) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21190 : oddCount 21190 15 = 7 ∧ acceleratedOrbit 15 21190 = 1417 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21190 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21190) = 3 ^ 7 * m + 1417 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21190.1, data_15_21190.2]

/-- Complete interval computation for depth 15, residue 21191. -/
theorem bounds_15_21191 : exactInterval 15 21191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21191 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21191) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21191 : oddCount 21191 15 = 7 ∧ acceleratedOrbit 15 21191 = 1415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21191 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21191) = 3 ^ 7 * m + 1415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21191.1, data_15_21191.2]

/-- Complete interval computation for depth 15, residue 21192. -/
theorem bounds_15_21192 : exactInterval 15 21192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21192 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21192) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21192 : oddCount 21192 15 = 7 ∧ acceleratedOrbit 15 21192 = 1417 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21192 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21192) = 3 ^ 7 * m + 1417 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21192.1, data_15_21192.2]

/-- Complete interval computation for depth 15, residue 21193. -/
theorem bounds_15_21193 : exactInterval 15 21193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21193 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21193) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21193 : oddCount 21193 15 = 7 ∧ acceleratedOrbit 15 21193 = 1415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21193 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21193) = 3 ^ 7 * m + 1415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21193.1, data_15_21193.2]

/-- Complete interval computation for depth 15, residue 21194. -/
theorem bounds_15_21194 : exactInterval 15 21194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21194 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21194) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21194 : oddCount 21194 15 = 7 ∧ acceleratedOrbit 15 21194 = 1417 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21194 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21194) = 3 ^ 7 * m + 1417 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21194.1, data_15_21194.2]

/-- Complete interval computation for depth 15, residue 21195. -/
theorem bounds_15_21195 : exactInterval 15 21195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21195 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21195) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21195 : oddCount 21195 15 = 7 ∧ acceleratedOrbit 15 21195 = 1415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21195 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21195) = 3 ^ 7 * m + 1415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21195.1, data_15_21195.2]

/-- Complete interval computation for depth 15, residue 21196. -/
theorem bounds_15_21196 : exactInterval 15 21196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21196 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21196) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21196 : oddCount 21196 15 = 7 ∧ acceleratedOrbit 15 21196 = 1417 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21196 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21196) = 3 ^ 7 * m + 1417 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21196.1, data_15_21196.2]

/-- Complete interval computation for depth 15, residue 21197. -/
theorem bounds_15_21197 : exactInterval 15 21197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21197 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21197) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21197 : oddCount 21197 15 = 7 ∧ acceleratedOrbit 15 21197 = 1417 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21197 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21197) = 3 ^ 7 * m + 1417 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21197.1, data_15_21197.2]

/-- Complete interval computation for depth 15, residue 21198. -/
theorem bounds_15_21198 : exactInterval 15 21198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21198 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21198) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21198 : oddCount 21198 15 = 11 ∧ acceleratedOrbit 15 21198 = 114614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21198 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21198) = 3 ^ 11 * m + 114614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21198.1, data_15_21198.2]

/-- Complete interval computation for depth 15, residue 21199. -/
theorem bounds_15_21199 : exactInterval 15 21199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21199 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21199) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21199 : oddCount 21199 15 = 11 ∧ acceleratedOrbit 15 21199 = 114614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21199 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21199) = 3 ^ 11 * m + 114614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21199.1, data_15_21199.2]

end Collatz.Research.PassageAtlas.Batch0647
