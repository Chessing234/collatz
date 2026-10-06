import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0800

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 26181. -/
theorem bounds_15_26181 : exactInterval 15 26181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26181 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26181) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26181 : oddCount 26181 15 = 6 ∧ acceleratedOrbit 15 26181 = 584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26181 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26181) = 3 ^ 6 * m + 584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26181.1, data_15_26181.2]

/-- Complete interval computation for depth 15, residue 26182. -/
theorem bounds_15_26182 : exactInterval 15 26182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26182 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26182) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26182 : oddCount 26182 15 = 6 ∧ acceleratedOrbit 15 26182 = 584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26182 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26182) = 3 ^ 6 * m + 584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26182.1, data_15_26182.2]

/-- Complete interval computation for depth 15, residue 26183. -/
theorem bounds_15_26183 : exactInterval 15 26183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26183 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26183) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26183 : oddCount 26183 15 = 8 ∧ acceleratedOrbit 15 26183 = 5243 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26183 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26183) = 3 ^ 8 * m + 5243 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26183.1, data_15_26183.2]

/-- Complete interval computation for depth 15, residue 26184. -/
theorem bounds_15_26184 : exactInterval 15 26184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26184 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26184) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26184 : oddCount 26184 15 = 6 ∧ acceleratedOrbit 15 26184 = 584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26184 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26184) = 3 ^ 6 * m + 584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26184.1, data_15_26184.2]

/-- Complete interval computation for depth 15, residue 26185. -/
theorem bounds_15_26185 : exactInterval 15 26185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26185 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26185) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26185 : oddCount 26185 15 = 9 ∧ acceleratedOrbit 15 26185 = 15731 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26185 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26185) = 3 ^ 9 * m + 15731 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26185.1, data_15_26185.2]

/-- Complete interval computation for depth 15, residue 26186. -/
theorem bounds_15_26186 : exactInterval 15 26186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26186 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26186) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26186 : oddCount 26186 15 = 6 ∧ acceleratedOrbit 15 26186 = 584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26186 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26186) = 3 ^ 6 * m + 584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26186.1, data_15_26186.2]

/-- Complete interval computation for depth 15, residue 26187. -/
theorem bounds_15_26187 : exactInterval 15 26187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26187 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26187) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26187 : oddCount 26187 15 = 6 ∧ acceleratedOrbit 15 26187 = 584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26187 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26187) = 3 ^ 6 * m + 584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26187.1, data_15_26187.2]

/-- Complete interval computation for depth 15, residue 26188. -/
theorem bounds_15_26188 : exactInterval 15 26188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26188 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26188) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26188 : oddCount 26188 15 = 6 ∧ acceleratedOrbit 15 26188 = 584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26188 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26188) = 3 ^ 6 * m + 584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26188.1, data_15_26188.2]

/-- Complete interval computation for depth 15, residue 26189. -/
theorem bounds_15_26189 : exactInterval 15 26189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26189 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26189) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26189 : oddCount 26189 15 = 6 ∧ acceleratedOrbit 15 26189 = 584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26189 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26189) = 3 ^ 6 * m + 584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26189.1, data_15_26189.2]

/-- Complete interval computation for depth 15, residue 26190. -/
theorem bounds_15_26190 : exactInterval 15 26190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26190 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26190) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26190 : oddCount 26190 15 = 9 ∧ acceleratedOrbit 15 26190 = 15734 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26190 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26190) = 3 ^ 9 * m + 15734 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26190.1, data_15_26190.2]

/-- Complete interval computation for depth 15, residue 26191. -/
theorem bounds_15_26191 : exactInterval 15 26191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26191 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26191) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26191 : oddCount 26191 15 = 9 ∧ acceleratedOrbit 15 26191 = 15734 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26191 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26191) = 3 ^ 9 * m + 15734 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26191.1, data_15_26191.2]

/-- Complete interval computation for depth 15, residue 26192. -/
theorem bounds_15_26192 : exactInterval 15 26192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26192 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26192) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26192 : oddCount 26192 15 = 4 ∧ acceleratedOrbit 15 26192 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26192 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26192) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26192.1, data_15_26192.2]

/-- Complete interval computation for depth 15, residue 26193. -/
theorem bounds_15_26193 : exactInterval 15 26193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26193 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26193) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26193 : oddCount 26193 15 = 8 ∧ acceleratedOrbit 15 26193 = 5246 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26193 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26193) = 3 ^ 8 * m + 5246 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26193.1, data_15_26193.2]

/-- Complete interval computation for depth 15, residue 26194. -/
theorem bounds_15_26194 : exactInterval 15 26194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26194 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26194) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26194 : oddCount 26194 15 = 8 ∧ acceleratedOrbit 15 26194 = 5246 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26194 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26194) = 3 ^ 8 * m + 5246 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26194.1, data_15_26194.2]

/-- Complete interval computation for depth 15, residue 26195. -/
theorem bounds_15_26195 : exactInterval 15 26195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26195 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26195) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26195 : oddCount 26195 15 = 8 ∧ acceleratedOrbit 15 26195 = 5246 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26195 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26195) = 3 ^ 8 * m + 5246 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26195.1, data_15_26195.2]

/-- Complete interval computation for depth 15, residue 26196. -/
theorem bounds_15_26196 : exactInterval 15 26196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26196 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26196) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26196 : oddCount 26196 15 = 4 ∧ acceleratedOrbit 15 26196 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26196 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26196) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26196.1, data_15_26196.2]

/-- Complete interval computation for depth 15, residue 26197. -/
theorem bounds_15_26197 : exactInterval 15 26197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26197 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26197) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26197 : oddCount 26197 15 = 4 ∧ acceleratedOrbit 15 26197 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26197 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26197) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26197.1, data_15_26197.2]

/-- Complete interval computation for depth 15, residue 26198. -/
theorem bounds_15_26198 : exactInterval 15 26198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26198 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26198) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26198 : oddCount 26198 15 = 6 ∧ acceleratedOrbit 15 26198 = 583 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26198 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26198) = 3 ^ 6 * m + 583 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26198.1, data_15_26198.2]

/-- Complete interval computation for depth 15, residue 26199. -/
theorem bounds_15_26199 : exactInterval 15 26199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26199 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26199) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26199 : oddCount 26199 15 = 6 ∧ acceleratedOrbit 15 26199 = 583 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26199 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26199) = 3 ^ 6 * m + 583 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26199.1, data_15_26199.2]

/-- Complete interval computation for depth 15, residue 26200. -/
theorem bounds_15_26200 : exactInterval 15 26200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26200 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26200) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26200 : oddCount 26200 15 = 6 ∧ acceleratedOrbit 15 26200 = 584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26200 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26200) = 3 ^ 6 * m + 584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26200.1, data_15_26200.2]

/-- Complete interval computation for depth 15, residue 26201. -/
theorem bounds_15_26201 : exactInterval 15 26201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26201 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26201) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26201 : oddCount 26201 15 = 6 ∧ acceleratedOrbit 15 26201 = 583 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26201 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26201) = 3 ^ 6 * m + 583 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26201.1, data_15_26201.2]

/-- Complete interval computation for depth 15, residue 26202. -/
theorem bounds_15_26202 : exactInterval 15 26202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26202 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26202) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26202 : oddCount 26202 15 = 6 ∧ acceleratedOrbit 15 26202 = 584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26202 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26202) = 3 ^ 6 * m + 584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26202.1, data_15_26202.2]

/-- Complete interval computation for depth 15, residue 26203. -/
theorem bounds_15_26203 : exactInterval 15 26203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26203 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26203) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26203 : oddCount 26203 15 = 11 ∧ acceleratedOrbit 15 26203 = 141668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26203 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26203) = 3 ^ 11 * m + 141668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26203.1, data_15_26203.2]

/-- Complete interval computation for depth 15, residue 26204. -/
theorem bounds_15_26204 : exactInterval 15 26204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26204 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26204) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26204 : oddCount 26204 15 = 6 ∧ acceleratedOrbit 15 26204 = 584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26204 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26204) = 3 ^ 6 * m + 584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26204.1, data_15_26204.2]

/-- Complete interval computation for depth 15, residue 26205. -/
theorem bounds_15_26205 : exactInterval 15 26205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26205 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26205) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26205 : oddCount 26205 15 = 6 ∧ acceleratedOrbit 15 26205 = 584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26205 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26205) = 3 ^ 6 * m + 584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26205.1, data_15_26205.2]

/-- Complete interval computation for depth 15, residue 26206. -/
theorem bounds_15_26206 : exactInterval 15 26206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26206 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26206) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26206 : oddCount 26206 15 = 8 ∧ acceleratedOrbit 15 26206 = 5248 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26206 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26206) = 3 ^ 8 * m + 5248 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26206.1, data_15_26206.2]

/-- Complete interval computation for depth 15, residue 26207. -/
theorem bounds_15_26207 : exactInterval 15 26207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26207 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26207) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26207 : oddCount 26207 15 = 8 ∧ acceleratedOrbit 15 26207 = 5248 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26207 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26207) = 3 ^ 8 * m + 5248 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26207.1, data_15_26207.2]

/-- Complete interval computation for depth 15, residue 26208. -/
theorem bounds_15_26208 : exactInterval 15 26208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26208 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26208) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26208 : oddCount 26208 15 = 4 ∧ acceleratedOrbit 15 26208 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26208 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26208) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26208.1, data_15_26208.2]

/-- Complete interval computation for depth 15, residue 26209. -/
theorem bounds_15_26209 : exactInterval 15 26209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26209 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26209) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26209 : oddCount 26209 15 = 7 ∧ acceleratedOrbit 15 26209 = 1750 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26209 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26209) = 3 ^ 7 * m + 1750 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26209.1, data_15_26209.2]

/-- Complete interval computation for depth 15, residue 26210. -/
theorem bounds_15_26210 : exactInterval 15 26210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26210 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26210) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26210 : oddCount 26210 15 = 6 ∧ acceleratedOrbit 15 26210 = 584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26210 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26210) = 3 ^ 6 * m + 584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26210.1, data_15_26210.2]

/-- Complete interval computation for depth 15, residue 26211. -/
theorem bounds_15_26211 : exactInterval 15 26211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26211 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26211) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26211 : oddCount 26211 15 = 6 ∧ acceleratedOrbit 15 26211 = 584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26211 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26211) = 3 ^ 6 * m + 584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26211.1, data_15_26211.2]

/-- Complete interval computation for depth 15, residue 26212. -/
theorem bounds_15_26212 : exactInterval 15 26212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26212 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26212) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26212 : oddCount 26212 15 = 6 ∧ acceleratedOrbit 15 26212 = 584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26212 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26212) = 3 ^ 6 * m + 584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26212.1, data_15_26212.2]

/-- Complete interval computation for depth 15, residue 26213. -/
theorem bounds_15_26213 : exactInterval 15 26213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26213 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26213) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26213 : oddCount 26213 15 = 6 ∧ acceleratedOrbit 15 26213 = 584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26213 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26213) = 3 ^ 6 * m + 584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26213.1, data_15_26213.2]

end Collatz.Research.PassageAtlas.Batch0800
