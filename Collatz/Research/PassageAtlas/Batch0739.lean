import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0739

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 24182. -/
theorem bounds_15_24182 : exactInterval 15 24182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24182 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24182) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24182 : oddCount 24182 15 = 7 ∧ acceleratedOrbit 15 24182 = 1615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24182 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24182) = 3 ^ 7 * m + 1615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24182.1, data_15_24182.2]

/-- Complete interval computation for depth 15, residue 24183. -/
theorem bounds_15_24183 : exactInterval 15 24183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24183 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24183) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24183 : oddCount 24183 15 = 7 ∧ acceleratedOrbit 15 24183 = 1615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24183 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24183) = 3 ^ 7 * m + 1615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24183.1, data_15_24183.2]

/-- Complete interval computation for depth 15, residue 24184. -/
theorem bounds_15_24184 : exactInterval 15 24184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24184 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24184) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24184 : oddCount 24184 15 = 7 ∧ acceleratedOrbit 15 24184 = 1615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24184 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24184) = 3 ^ 7 * m + 1615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24184.1, data_15_24184.2]

/-- Complete interval computation for depth 15, residue 24185. -/
theorem bounds_15_24185 : exactInterval 15 24185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24185 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24185) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24185 : oddCount 24185 15 = 8 ∧ acceleratedOrbit 15 24185 = 4843 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24185 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24185) = 3 ^ 8 * m + 4843 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24185.1, data_15_24185.2]

/-- Complete interval computation for depth 15, residue 24186. -/
theorem bounds_15_24186 : exactInterval 15 24186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24186 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24186) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24186 : oddCount 24186 15 = 7 ∧ acceleratedOrbit 15 24186 = 1615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24186 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24186) = 3 ^ 7 * m + 1615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24186.1, data_15_24186.2]

/-- Complete interval computation for depth 15, residue 24187. -/
theorem bounds_15_24187 : exactInterval 15 24187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24187 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24187) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24187 : oddCount 24187 15 = 7 ∧ acceleratedOrbit 15 24187 = 1615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24187 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24187) = 3 ^ 7 * m + 1615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24187.1, data_15_24187.2]

/-- Complete interval computation for depth 15, residue 24188. -/
theorem bounds_15_24188 : exactInterval 15 24188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24188 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24188) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24188 : oddCount 24188 15 = 8 ∧ acceleratedOrbit 15 24188 = 4844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24188 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24188) = 3 ^ 8 * m + 4844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24188.1, data_15_24188.2]

/-- Complete interval computation for depth 15, residue 24189. -/
theorem bounds_15_24189 : exactInterval 15 24189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24189 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24189) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24189 : oddCount 24189 15 = 8 ∧ acceleratedOrbit 15 24189 = 4844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24189 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24189) = 3 ^ 8 * m + 4844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24189.1, data_15_24189.2]

/-- Complete interval computation for depth 15, residue 24190. -/
theorem bounds_15_24190 : exactInterval 15 24190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24190 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24190) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24190 : oddCount 24190 15 = 8 ∧ acceleratedOrbit 15 24190 = 4844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24190 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24190) = 3 ^ 8 * m + 4844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24190.1, data_15_24190.2]

/-- Complete interval computation for depth 15, residue 24191. -/
theorem bounds_15_24191 : exactInterval 15 24191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24191 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24191) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24191 : oddCount 24191 15 = 12 ∧ acceleratedOrbit 15 24191 = 392354 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24191 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24191) = 3 ^ 12 * m + 392354 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24191.1, data_15_24191.2]

/-- Complete interval computation for depth 15, residue 24192. -/
theorem bounds_15_24192 : exactInterval 15 24192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24192 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24192) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24192 : oddCount 24192 15 = 5 ∧ acceleratedOrbit 15 24192 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24192 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24192) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24192.1, data_15_24192.2]

/-- Complete interval computation for depth 15, residue 24193. -/
theorem bounds_15_24193 : exactInterval 15 24193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24193 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24193) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24193 : oddCount 24193 15 = 10 ∧ acceleratedOrbit 15 24193 = 43604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24193 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24193) = 3 ^ 10 * m + 43604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24193.1, data_15_24193.2]

/-- Complete interval computation for depth 15, residue 24194. -/
theorem bounds_15_24194 : exactInterval 15 24194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24194 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24194) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24194 : oddCount 24194 15 = 7 ∧ acceleratedOrbit 15 24194 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24194 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24194) = 3 ^ 7 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24194.1, data_15_24194.2]

/-- Complete interval computation for depth 15, residue 24195. -/
theorem bounds_15_24195 : exactInterval 15 24195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24195 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24195) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24195 : oddCount 24195 15 = 7 ∧ acceleratedOrbit 15 24195 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24195 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24195) = 3 ^ 7 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24195.1, data_15_24195.2]

/-- Complete interval computation for depth 15, residue 24196. -/
theorem bounds_15_24196 : exactInterval 15 24196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24196 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24196) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24196 : oddCount 24196 15 = 6 ∧ acceleratedOrbit 15 24196 = 539 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24196 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24196) = 3 ^ 6 * m + 539 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24196.1, data_15_24196.2]

/-- Complete interval computation for depth 15, residue 24197. -/
theorem bounds_15_24197 : exactInterval 15 24197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24197 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24197) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24197 : oddCount 24197 15 = 6 ∧ acceleratedOrbit 15 24197 = 539 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24197 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24197) = 3 ^ 6 * m + 539 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24197.1, data_15_24197.2]

/-- Complete interval computation for depth 15, residue 24198. -/
theorem bounds_15_24198 : exactInterval 15 24198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24198 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24198) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24198 : oddCount 24198 15 = 6 ∧ acceleratedOrbit 15 24198 = 539 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24198 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24198) = 3 ^ 6 * m + 539 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24198.1, data_15_24198.2]

/-- Complete interval computation for depth 15, residue 24199. -/
theorem bounds_15_24199 : exactInterval 15 24199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24199 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24199) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24199 : oddCount 24199 15 = 9 ∧ acceleratedOrbit 15 24199 = 14539 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24199 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24199) = 3 ^ 9 * m + 14539 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24199.1, data_15_24199.2]

/-- Complete interval computation for depth 15, residue 24200. -/
theorem bounds_15_24200 : exactInterval 15 24200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24200 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24200) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24200 : oddCount 24200 15 = 7 ∧ acceleratedOrbit 15 24200 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24200 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24200) = 3 ^ 7 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24200.1, data_15_24200.2]

/-- Complete interval computation for depth 15, residue 24201. -/
theorem bounds_15_24201 : exactInterval 15 24201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24201 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24201) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24201 : oddCount 24201 15 = 10 ∧ acceleratedOrbit 15 24201 = 43615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24201 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24201) = 3 ^ 10 * m + 43615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24201.1, data_15_24201.2]

/-- Complete interval computation for depth 15, residue 24202. -/
theorem bounds_15_24202 : exactInterval 15 24202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24202 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24202) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24202 : oddCount 24202 15 = 7 ∧ acceleratedOrbit 15 24202 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24202 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24202) = 3 ^ 7 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24202.1, data_15_24202.2]

/-- Complete interval computation for depth 15, residue 24203. -/
theorem bounds_15_24203 : exactInterval 15 24203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24203 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24203) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24203 : oddCount 24203 15 = 6 ∧ acceleratedOrbit 15 24203 = 539 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24203 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24203) = 3 ^ 6 * m + 539 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24203.1, data_15_24203.2]

/-- Complete interval computation for depth 15, residue 24204. -/
theorem bounds_15_24204 : exactInterval 15 24204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24204 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24204) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24204 : oddCount 24204 15 = 7 ∧ acceleratedOrbit 15 24204 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24204 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24204) = 3 ^ 7 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24204.1, data_15_24204.2]

/-- Complete interval computation for depth 15, residue 24205. -/
theorem bounds_15_24205 : exactInterval 15 24205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24205 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24205) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24205 : oddCount 24205 15 = 7 ∧ acceleratedOrbit 15 24205 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24205 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24205) = 3 ^ 7 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24205.1, data_15_24205.2]

/-- Complete interval computation for depth 15, residue 24206. -/
theorem bounds_15_24206 : exactInterval 15 24206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24206 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24206) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24206 : oddCount 24206 15 = 9 ∧ acceleratedOrbit 15 24206 = 14543 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24206 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24206) = 3 ^ 9 * m + 14543 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24206.1, data_15_24206.2]

/-- Complete interval computation for depth 15, residue 24207. -/
theorem bounds_15_24207 : exactInterval 15 24207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24207 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24207) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24207 : oddCount 24207 15 = 9 ∧ acceleratedOrbit 15 24207 = 14543 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24207 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24207) = 3 ^ 9 * m + 14543 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24207.1, data_15_24207.2]

/-- Complete interval computation for depth 15, residue 24208. -/
theorem bounds_15_24208 : exactInterval 15 24208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24208 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24208) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24208 : oddCount 24208 15 = 8 ∧ acceleratedOrbit 15 24208 = 4853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24208 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24208) = 3 ^ 8 * m + 4853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24208.1, data_15_24208.2]

/-- Complete interval computation for depth 15, residue 24209. -/
theorem bounds_15_24209 : exactInterval 15 24209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24209 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24209) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24209 : oddCount 24209 15 = 8 ∧ acceleratedOrbit 15 24209 = 4850 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24209 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24209) = 3 ^ 8 * m + 4850 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24209.1, data_15_24209.2]

/-- Complete interval computation for depth 15, residue 24210. -/
theorem bounds_15_24210 : exactInterval 15 24210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24210 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24210) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24210 : oddCount 24210 15 = 8 ∧ acceleratedOrbit 15 24210 = 4850 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24210 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24210) = 3 ^ 8 * m + 4850 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24210.1, data_15_24210.2]

/-- Complete interval computation for depth 15, residue 24211. -/
theorem bounds_15_24211 : exactInterval 15 24211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24211 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24211) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24211 : oddCount 24211 15 = 8 ∧ acceleratedOrbit 15 24211 = 4850 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24211 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24211) = 3 ^ 8 * m + 4850 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24211.1, data_15_24211.2]

/-- Complete interval computation for depth 15, residue 24212. -/
theorem bounds_15_24212 : exactInterval 15 24212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24212 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24212) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24212 : oddCount 24212 15 = 8 ∧ acceleratedOrbit 15 24212 = 4853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24212 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24212) = 3 ^ 8 * m + 4853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24212.1, data_15_24212.2]

/-- Complete interval computation for depth 15, residue 24213. -/
theorem bounds_15_24213 : exactInterval 15 24213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24213 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24213) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24213 : oddCount 24213 15 = 8 ∧ acceleratedOrbit 15 24213 = 4853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24213 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24213) = 3 ^ 8 * m + 4853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24213.1, data_15_24213.2]

/-- Complete interval computation for depth 15, residue 24214. -/
theorem bounds_15_24214 : exactInterval 15 24214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24214 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24214) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24214 : oddCount 24214 15 = 7 ∧ acceleratedOrbit 15 24214 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24214 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24214) = 3 ^ 7 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24214.1, data_15_24214.2]

end Collatz.Research.PassageAtlas.Batch0739
