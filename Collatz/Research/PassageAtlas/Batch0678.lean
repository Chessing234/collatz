import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0678

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 22183. -/
theorem bounds_15_22183 : exactInterval 15 22183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22183 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22183) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22183 : oddCount 22183 15 = 8 ∧ acceleratedOrbit 15 22183 = 4442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22183 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22183) = 3 ^ 8 * m + 4442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22183.1, data_15_22183.2]

/-- Complete interval computation for depth 15, residue 22184. -/
theorem bounds_15_22184 : exactInterval 15 22184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22184 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22184) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22184 : oddCount 22184 15 = 4 ∧ acceleratedOrbit 15 22184 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22184 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22184) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22184.1, data_15_22184.2]

/-- Complete interval computation for depth 15, residue 22185. -/
theorem bounds_15_22185 : exactInterval 15 22185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22185 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22185) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22185 : oddCount 22185 15 = 9 ∧ acceleratedOrbit 15 22185 = 13327 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22185 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22185) = 3 ^ 9 * m + 13327 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22185.1, data_15_22185.2]

/-- Complete interval computation for depth 15, residue 22186. -/
theorem bounds_15_22186 : exactInterval 15 22186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22186 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22186) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22186 : oddCount 22186 15 = 4 ∧ acceleratedOrbit 15 22186 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22186 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22186) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22186.1, data_15_22186.2]

/-- Complete interval computation for depth 15, residue 22187. -/
theorem bounds_15_22187 : exactInterval 15 22187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22187 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22187) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22187 : oddCount 22187 15 = 7 ∧ acceleratedOrbit 15 22187 = 1481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22187 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22187) = 3 ^ 7 * m + 1481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22187.1, data_15_22187.2]

/-- Complete interval computation for depth 15, residue 22188. -/
theorem bounds_15_22188 : exactInterval 15 22188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22188 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22188) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22188 : oddCount 22188 15 = 8 ∧ acceleratedOrbit 15 22188 = 4445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22188 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22188) = 3 ^ 8 * m + 4445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22188.1, data_15_22188.2]

/-- Complete interval computation for depth 15, residue 22189. -/
theorem bounds_15_22189 : exactInterval 15 22189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22189 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22189) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22189 : oddCount 22189 15 = 8 ∧ acceleratedOrbit 15 22189 = 4445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22189 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22189) = 3 ^ 8 * m + 4445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22189.1, data_15_22189.2]

/-- Complete interval computation for depth 15, residue 22190. -/
theorem bounds_15_22190 : exactInterval 15 22190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22190 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22190) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22190 : oddCount 22190 15 = 8 ∧ acceleratedOrbit 15 22190 = 4445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22190 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22190) = 3 ^ 8 * m + 4445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22190.1, data_15_22190.2]

/-- Complete interval computation for depth 15, residue 22191. -/
theorem bounds_15_22191 : exactInterval 15 22191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22191 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22191) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22191 : oddCount 22191 15 = 9 ∧ acceleratedOrbit 15 22191 = 13331 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22191 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22191) = 3 ^ 9 * m + 13331 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22191.1, data_15_22191.2]

/-- Complete interval computation for depth 15, residue 22192. -/
theorem bounds_15_22192 : exactInterval 15 22192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22192 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22192) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22192 : oddCount 22192 15 = 7 ∧ acceleratedOrbit 15 22192 = 1484 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22192 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22192) = 3 ^ 7 * m + 1484 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22192.1, data_15_22192.2]

/-- Complete interval computation for depth 15, residue 22193. -/
theorem bounds_15_22193 : exactInterval 15 22193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22193 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22193) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22193 : oddCount 22193 15 = 7 ∧ acceleratedOrbit 15 22193 = 1484 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22193 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22193) = 3 ^ 7 * m + 1484 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22193.1, data_15_22193.2]

/-- Complete interval computation for depth 15, residue 22194. -/
theorem bounds_15_22194 : exactInterval 15 22194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22194 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22194) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22194 : oddCount 22194 15 = 7 ∧ acceleratedOrbit 15 22194 = 1484 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22194 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22194) = 3 ^ 7 * m + 1484 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22194.1, data_15_22194.2]

/-- Complete interval computation for depth 15, residue 22195. -/
theorem bounds_15_22195 : exactInterval 15 22195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22195 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22195) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22195 : oddCount 22195 15 = 7 ∧ acceleratedOrbit 15 22195 = 1484 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22195 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22195) = 3 ^ 7 * m + 1484 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22195.1, data_15_22195.2]

/-- Complete interval computation for depth 15, residue 22196. -/
theorem bounds_15_22196 : exactInterval 15 22196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22196 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22196) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22196 : oddCount 22196 15 = 7 ∧ acceleratedOrbit 15 22196 = 1484 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22196 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22196) = 3 ^ 7 * m + 1484 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22196.1, data_15_22196.2]

/-- Complete interval computation for depth 15, residue 22197. -/
theorem bounds_15_22197 : exactInterval 15 22197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22197 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22197) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22197 : oddCount 22197 15 = 7 ∧ acceleratedOrbit 15 22197 = 1484 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22197 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22197) = 3 ^ 7 * m + 1484 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22197.1, data_15_22197.2]

/-- Complete interval computation for depth 15, residue 22198. -/
theorem bounds_15_22198 : exactInterval 15 22198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22198 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22198) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22198 : oddCount 22198 15 = 9 ∧ acceleratedOrbit 15 22198 = 13337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22198 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22198) = 3 ^ 9 * m + 13337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22198.1, data_15_22198.2]

/-- Complete interval computation for depth 15, residue 22199. -/
theorem bounds_15_22199 : exactInterval 15 22199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22199 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22199) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22199 : oddCount 22199 15 = 9 ∧ acceleratedOrbit 15 22199 = 13337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22199 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22199) = 3 ^ 9 * m + 13337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22199.1, data_15_22199.2]

/-- Complete interval computation for depth 15, residue 22200. -/
theorem bounds_15_22200 : exactInterval 15 22200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22200 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22200) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22200 : oddCount 22200 15 = 7 ∧ acceleratedOrbit 15 22200 = 1484 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22200 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22200) = 3 ^ 7 * m + 1484 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22200.1, data_15_22200.2]

/-- Complete interval computation for depth 15, residue 22201. -/
theorem bounds_15_22201 : exactInterval 15 22201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22201 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22201) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22201 : oddCount 22201 15 = 6 ∧ acceleratedOrbit 15 22201 = 494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22201 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22201) = 3 ^ 6 * m + 494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22201.1, data_15_22201.2]

/-- Complete interval computation for depth 15, residue 22202. -/
theorem bounds_15_22202 : exactInterval 15 22202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22202 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22202) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22202 : oddCount 22202 15 = 7 ∧ acceleratedOrbit 15 22202 = 1484 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22202 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22202) = 3 ^ 7 * m + 1484 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22202.1, data_15_22202.2]

/-- Complete interval computation for depth 15, residue 22203. -/
theorem bounds_15_22203 : exactInterval 15 22203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22203 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22203) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22203 : oddCount 22203 15 = 6 ∧ acceleratedOrbit 15 22203 = 494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22203 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22203) = 3 ^ 6 * m + 494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22203.1, data_15_22203.2]

/-- Complete interval computation for depth 15, residue 22204. -/
theorem bounds_15_22204 : exactInterval 15 22204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22204 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22204) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22204 : oddCount 22204 15 = 8 ∧ acceleratedOrbit 15 22204 = 4448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22204 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22204) = 3 ^ 8 * m + 4448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22204.1, data_15_22204.2]

/-- Complete interval computation for depth 15, residue 22205. -/
theorem bounds_15_22205 : exactInterval 15 22205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22205 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22205) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22205 : oddCount 22205 15 = 8 ∧ acceleratedOrbit 15 22205 = 4448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22205 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22205) = 3 ^ 8 * m + 4448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22205.1, data_15_22205.2]

/-- Complete interval computation for depth 15, residue 22206. -/
theorem bounds_15_22206 : exactInterval 15 22206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22206 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22206) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22206 : oddCount 22206 15 = 8 ∧ acceleratedOrbit 15 22206 = 4448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22206 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22206) = 3 ^ 8 * m + 4448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22206.1, data_15_22206.2]

/-- Complete interval computation for depth 15, residue 22207. -/
theorem bounds_15_22207 : exactInterval 15 22207 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22207 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22207) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22207 : oddCount 22207 15 = 9 ∧ acceleratedOrbit 15 22207 = 13340 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22207 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22207) = 3 ^ 9 * m + 13340 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22207.1, data_15_22207.2]

/-- Complete interval computation for depth 15, residue 22208. -/
theorem bounds_15_22208 : exactInterval 15 22208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22208 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22208) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22208 : oddCount 22208 15 = 6 ∧ acceleratedOrbit 15 22208 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22208 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22208) = 3 ^ 6 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22208.1, data_15_22208.2]

/-- Complete interval computation for depth 15, residue 22209. -/
theorem bounds_15_22209 : exactInterval 15 22209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22209 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22209) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22209 : oddCount 22209 15 = 7 ∧ acceleratedOrbit 15 22209 = 1484 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22209 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22209) = 3 ^ 7 * m + 1484 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22209.1, data_15_22209.2]

/-- Complete interval computation for depth 15, residue 22210. -/
theorem bounds_15_22210 : exactInterval 15 22210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22210 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22210) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22210 : oddCount 22210 15 = 10 ∧ acceleratedOrbit 15 22210 = 40034 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22210 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22210) = 3 ^ 10 * m + 40034 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22210.1, data_15_22210.2]

/-- Complete interval computation for depth 15, residue 22211. -/
theorem bounds_15_22211 : exactInterval 15 22211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22211 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22211) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22211 : oddCount 22211 15 = 10 ∧ acceleratedOrbit 15 22211 = 40034 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22211 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22211) = 3 ^ 10 * m + 40034 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22211.1, data_15_22211.2]

/-- Complete interval computation for depth 15, residue 22212. -/
theorem bounds_15_22212 : exactInterval 15 22212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22212 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22212) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22212 : oddCount 22212 15 = 4 ∧ acceleratedOrbit 15 22212 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22212 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22212) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22212.1, data_15_22212.2]

/-- Complete interval computation for depth 15, residue 22213. -/
theorem bounds_15_22213 : exactInterval 15 22213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22213 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22213) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22213 : oddCount 22213 15 = 4 ∧ acceleratedOrbit 15 22213 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22213 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22213) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22213.1, data_15_22213.2]

/-- Complete interval computation for depth 15, residue 22214. -/
theorem bounds_15_22214 : exactInterval 15 22214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22214 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22214) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22214 : oddCount 22214 15 = 4 ∧ acceleratedOrbit 15 22214 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22214 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22214) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22214.1, data_15_22214.2]

/-- Complete interval computation for depth 15, residue 22215. -/
theorem bounds_15_22215 : exactInterval 15 22215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22215 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22215) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22215 : oddCount 22215 15 = 7 ∧ acceleratedOrbit 15 22215 = 1484 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22215 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22215) = 3 ^ 7 * m + 1484 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22215.1, data_15_22215.2]

end Collatz.Research.PassageAtlas.Batch0678
