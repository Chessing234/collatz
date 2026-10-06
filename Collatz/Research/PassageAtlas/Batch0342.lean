import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0342

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 11173. -/
theorem bounds_15_11173 : exactInterval 15 11173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11173 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11173) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11173 : oddCount 11173 15 = 9 ∧ acceleratedOrbit 15 11173 = 6716 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11173 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11173) = 3 ^ 9 * m + 6716 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11173.1, data_15_11173.2]

/-- Complete interval computation for depth 15, residue 11174. -/
theorem bounds_15_11174 : exactInterval 15 11174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11174 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11174) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11174 : oddCount 11174 15 = 9 ∧ acceleratedOrbit 15 11174 = 6716 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11174 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11174) = 3 ^ 9 * m + 6716 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11174.1, data_15_11174.2]

/-- Complete interval computation for depth 15, residue 11175. -/
theorem bounds_15_11175 : exactInterval 15 11175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11175 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11175) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11175 : oddCount 11175 15 = 11 ∧ acceleratedOrbit 15 11175 = 60425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11175 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11175) = 3 ^ 11 * m + 60425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11175.1, data_15_11175.2]

/-- Complete interval computation for depth 15, residue 11176. -/
theorem bounds_15_11176 : exactInterval 15 11176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11176 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11176) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11176 : oddCount 11176 15 = 4 ∧ acceleratedOrbit 15 11176 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11176 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11176) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11176.1, data_15_11176.2]

/-- Complete interval computation for depth 15, residue 11177. -/
theorem bounds_15_11177 : exactInterval 15 11177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11177 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11177) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11177 : oddCount 11177 15 = 9 ∧ acceleratedOrbit 15 11177 = 6715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11177 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11177) = 3 ^ 9 * m + 6715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11177.1, data_15_11177.2]

/-- Complete interval computation for depth 15, residue 11178. -/
theorem bounds_15_11178 : exactInterval 15 11178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11178 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11178) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11178 : oddCount 11178 15 = 4 ∧ acceleratedOrbit 15 11178 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11178 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11178) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11178.1, data_15_11178.2]

/-- Complete interval computation for depth 15, residue 11179. -/
theorem bounds_15_11179 : exactInterval 15 11179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11179 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11179) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11179 : oddCount 11179 15 = 8 ∧ acceleratedOrbit 15 11179 = 2240 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11179 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11179) = 3 ^ 8 * m + 2240 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11179.1, data_15_11179.2]

/-- Complete interval computation for depth 15, residue 11180. -/
theorem bounds_15_11180 : exactInterval 15 11180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11180 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11180) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11180 : oddCount 11180 15 = 9 ∧ acceleratedOrbit 15 11180 = 6722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11180 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11180) = 3 ^ 9 * m + 6722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11180.1, data_15_11180.2]

/-- Complete interval computation for depth 15, residue 11181. -/
theorem bounds_15_11181 : exactInterval 15 11181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11181 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11181) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11181 : oddCount 11181 15 = 9 ∧ acceleratedOrbit 15 11181 = 6722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11181 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11181) = 3 ^ 9 * m + 6722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11181.1, data_15_11181.2]

/-- Complete interval computation for depth 15, residue 11182. -/
theorem bounds_15_11182 : exactInterval 15 11182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11182 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11182) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11182 : oddCount 11182 15 = 9 ∧ acceleratedOrbit 15 11182 = 6722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11182 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11182) = 3 ^ 9 * m + 6722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11182.1, data_15_11182.2]

/-- Complete interval computation for depth 15, residue 11183. -/
theorem bounds_15_11183 : exactInterval 15 11183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11183 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11183) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11183 : oddCount 11183 15 = 9 ∧ acceleratedOrbit 15 11183 = 6722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11183 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11183) = 3 ^ 9 * m + 6722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11183.1, data_15_11183.2]

/-- Complete interval computation for depth 15, residue 11184. -/
theorem bounds_15_11184 : exactInterval 15 11184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11184 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11184) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11184 : oddCount 11184 15 = 7 ∧ acceleratedOrbit 15 11184 = 749 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11184 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11184) = 3 ^ 7 * m + 749 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11184.1, data_15_11184.2]

/-- Complete interval computation for depth 15, residue 11185. -/
theorem bounds_15_11185 : exactInterval 15 11185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11185 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11185) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11185 : oddCount 11185 15 = 7 ∧ acceleratedOrbit 15 11185 = 749 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11185 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11185) = 3 ^ 7 * m + 749 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11185.1, data_15_11185.2]

/-- Complete interval computation for depth 15, residue 11186. -/
theorem bounds_15_11186 : exactInterval 15 11186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11186 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11186) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11186 : oddCount 11186 15 = 7 ∧ acceleratedOrbit 15 11186 = 749 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11186 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11186) = 3 ^ 7 * m + 749 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11186.1, data_15_11186.2]

/-- Complete interval computation for depth 15, residue 11187. -/
theorem bounds_15_11187 : exactInterval 15 11187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11187 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11187) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11187 : oddCount 11187 15 = 7 ∧ acceleratedOrbit 15 11187 = 749 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11187 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11187) = 3 ^ 7 * m + 749 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11187.1, data_15_11187.2]

/-- Complete interval computation for depth 15, residue 11188. -/
theorem bounds_15_11188 : exactInterval 15 11188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11188 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11188) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11188 : oddCount 11188 15 = 7 ∧ acceleratedOrbit 15 11188 = 749 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11188 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11188) = 3 ^ 7 * m + 749 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11188.1, data_15_11188.2]

/-- Complete interval computation for depth 15, residue 11189. -/
theorem bounds_15_11189 : exactInterval 15 11189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11189 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11189) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11189 : oddCount 11189 15 = 7 ∧ acceleratedOrbit 15 11189 = 749 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11189 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11189) = 3 ^ 7 * m + 749 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11189.1, data_15_11189.2]

/-- Complete interval computation for depth 15, residue 11190. -/
theorem bounds_15_11190 : exactInterval 15 11190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11190 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11190) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11190 : oddCount 11190 15 = 5 ∧ acceleratedOrbit 15 11190 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11190 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11190) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11190.1, data_15_11190.2]

/-- Complete interval computation for depth 15, residue 11191. -/
theorem bounds_15_11191 : exactInterval 15 11191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11191 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11191) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11191 : oddCount 11191 15 = 5 ∧ acceleratedOrbit 15 11191 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11191 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11191) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11191.1, data_15_11191.2]

/-- Complete interval computation for depth 15, residue 11192. -/
theorem bounds_15_11192 : exactInterval 15 11192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11192 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11192) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11192 : oddCount 11192 15 = 7 ∧ acceleratedOrbit 15 11192 = 749 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11192 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11192) = 3 ^ 7 * m + 749 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11192.1, data_15_11192.2]

/-- Complete interval computation for depth 15, residue 11193. -/
theorem bounds_15_11193 : exactInterval 15 11193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11193 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11193) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11193 : oddCount 11193 15 = 8 ∧ acceleratedOrbit 15 11193 = 2243 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11193 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11193) = 3 ^ 8 * m + 2243 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11193.1, data_15_11193.2]

/-- Complete interval computation for depth 15, residue 11194. -/
theorem bounds_15_11194 : exactInterval 15 11194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11194 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11194) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11194 : oddCount 11194 15 = 7 ∧ acceleratedOrbit 15 11194 = 749 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11194 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11194) = 3 ^ 7 * m + 749 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11194.1, data_15_11194.2]

/-- Complete interval computation for depth 15, residue 11195. -/
theorem bounds_15_11195 : exactInterval 15 11195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11195 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11195) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11195 : oddCount 11195 15 = 8 ∧ acceleratedOrbit 15 11195 = 2243 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11195 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11195) = 3 ^ 8 * m + 2243 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11195.1, data_15_11195.2]

/-- Complete interval computation for depth 15, residue 11196. -/
theorem bounds_15_11196 : exactInterval 15 11196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11196 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11196) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11196 : oddCount 11196 15 = 9 ∧ acceleratedOrbit 15 11196 = 6728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11196 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11196) = 3 ^ 9 * m + 6728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11196.1, data_15_11196.2]

/-- Complete interval computation for depth 15, residue 11197. -/
theorem bounds_15_11197 : exactInterval 15 11197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11197 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11197) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11197 : oddCount 11197 15 = 9 ∧ acceleratedOrbit 15 11197 = 6728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11197 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11197) = 3 ^ 9 * m + 6728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11197.1, data_15_11197.2]

/-- Complete interval computation for depth 15, residue 11198. -/
theorem bounds_15_11198 : exactInterval 15 11198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11198 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11198) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11198 : oddCount 11198 15 = 9 ∧ acceleratedOrbit 15 11198 = 6728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11198 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11198) = 3 ^ 9 * m + 6728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11198.1, data_15_11198.2]

/-- Complete interval computation for depth 15, residue 11199. -/
theorem bounds_15_11199 : exactInterval 15 11199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11199 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11199) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11199 : oddCount 11199 15 = 10 ∧ acceleratedOrbit 15 11199 = 20183 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11199 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11199) = 3 ^ 10 * m + 20183 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11199.1, data_15_11199.2]

/-- Complete interval computation for depth 15, residue 11200. -/
theorem bounds_15_11200 : exactInterval 15 11200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11200 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11200) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11200 : oddCount 11200 15 = 6 ∧ acceleratedOrbit 15 11200 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11200 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11200) = 3 ^ 6 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11200.1, data_15_11200.2]

/-- Complete interval computation for depth 15, residue 11201. -/
theorem bounds_15_11201 : exactInterval 15 11201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11201 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11201) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11201 : oddCount 11201 15 = 7 ∧ acceleratedOrbit 15 11201 = 748 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11201 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11201) = 3 ^ 7 * m + 748 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11201.1, data_15_11201.2]

/-- Complete interval computation for depth 15, residue 11202. -/
theorem bounds_15_11202 : exactInterval 15 11202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11202 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11202) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11202 : oddCount 11202 15 = 7 ∧ acceleratedOrbit 15 11202 = 748 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11202 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11202) = 3 ^ 7 * m + 748 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11202.1, data_15_11202.2]

/-- Complete interval computation for depth 15, residue 11203. -/
theorem bounds_15_11203 : exactInterval 15 11203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11203 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11203) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11203 : oddCount 11203 15 = 7 ∧ acceleratedOrbit 15 11203 = 748 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11203 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11203) = 3 ^ 7 * m + 748 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11203.1, data_15_11203.2]

/-- Complete interval computation for depth 15, residue 11204. -/
theorem bounds_15_11204 : exactInterval 15 11204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11204 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11204) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11204 : oddCount 11204 15 = 4 ∧ acceleratedOrbit 15 11204 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11204 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11204) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11204.1, data_15_11204.2]

/-- Complete interval computation for depth 15, residue 11205. -/
theorem bounds_15_11205 : exactInterval 15 11205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11205 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11205) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11205 : oddCount 11205 15 = 4 ∧ acceleratedOrbit 15 11205 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11205 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11205) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11205.1, data_15_11205.2]

end Collatz.Research.PassageAtlas.Batch0342
