import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0281

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 9175. -/
theorem bounds_15_9175 : exactInterval 15 9175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9175 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9175) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9175 : oddCount 9175 15 = 9 ∧ acceleratedOrbit 15 9175 = 5513 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9175 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9175) = 3 ^ 9 * m + 5513 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9175.1, data_15_9175.2]

/-- Complete interval computation for depth 15, residue 9176. -/
theorem bounds_15_9176 : exactInterval 15 9176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9176 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9176) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9176 : oddCount 9176 15 = 7 ∧ acceleratedOrbit 15 9176 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9176 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9176) = 3 ^ 7 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9176.1, data_15_9176.2]

/-- Complete interval computation for depth 15, residue 9177. -/
theorem bounds_15_9177 : exactInterval 15 9177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9177 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9177) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9177 : oddCount 9177 15 = 6 ∧ acceleratedOrbit 15 9177 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9177 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9177) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9177.1, data_15_9177.2]

/-- Complete interval computation for depth 15, residue 9178. -/
theorem bounds_15_9178 : exactInterval 15 9178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9178 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9178) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9178 : oddCount 9178 15 = 7 ∧ acceleratedOrbit 15 9178 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9178 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9178) = 3 ^ 7 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9178.1, data_15_9178.2]

/-- Complete interval computation for depth 15, residue 9179. -/
theorem bounds_15_9179 : exactInterval 15 9179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9179 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9179) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9179 : oddCount 9179 15 = 7 ∧ acceleratedOrbit 15 9179 = 613 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9179 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9179) = 3 ^ 7 * m + 613 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9179.1, data_15_9179.2]

/-- Complete interval computation for depth 15, residue 9180. -/
theorem bounds_15_9180 : exactInterval 15 9180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9180 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9180) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9180 : oddCount 9180 15 = 7 ∧ acceleratedOrbit 15 9180 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9180 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9180) = 3 ^ 7 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9180.1, data_15_9180.2]

/-- Complete interval computation for depth 15, residue 9181. -/
theorem bounds_15_9181 : exactInterval 15 9181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9181 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9181) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9181 : oddCount 9181 15 = 7 ∧ acceleratedOrbit 15 9181 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9181 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9181) = 3 ^ 7 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9181.1, data_15_9181.2]

/-- Complete interval computation for depth 15, residue 9182. -/
theorem bounds_15_9182 : exactInterval 15 9182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9182 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9182) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9182 : oddCount 9182 15 = 12 ∧ acceleratedOrbit 15 9182 = 148958 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9182 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9182) = 3 ^ 12 * m + 148958 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9182.1, data_15_9182.2]

/-- Complete interval computation for depth 15, residue 9183. -/
theorem bounds_15_9183 : exactInterval 15 9183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9183 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9183) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9183 : oddCount 9183 15 = 12 ∧ acceleratedOrbit 15 9183 = 148958 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9183 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9183) = 3 ^ 12 * m + 148958 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9183.1, data_15_9183.2]

/-- Complete interval computation for depth 15, residue 9184. -/
theorem bounds_15_9184 : exactInterval 15 9184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9184 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9184) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9184 : oddCount 9184 15 = 6 ∧ acceleratedOrbit 15 9184 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9184 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9184) = 3 ^ 6 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9184.1, data_15_9184.2]

/-- Complete interval computation for depth 15, residue 9185. -/
theorem bounds_15_9185 : exactInterval 15 9185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9185 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9185) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9185 : oddCount 9185 15 = 9 ∧ acceleratedOrbit 15 9185 = 5519 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9185 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9185) = 3 ^ 9 * m + 5519 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9185.1, data_15_9185.2]

/-- Complete interval computation for depth 15, residue 9186. -/
theorem bounds_15_9186 : exactInterval 15 9186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9186 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9186) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9186 : oddCount 9186 15 = 6 ∧ acceleratedOrbit 15 9186 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9186 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9186) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9186.1, data_15_9186.2]

/-- Complete interval computation for depth 15, residue 9187. -/
theorem bounds_15_9187 : exactInterval 15 9187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9187 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9187) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9187 : oddCount 9187 15 = 6 ∧ acceleratedOrbit 15 9187 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9187 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9187) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9187.1, data_15_9187.2]

/-- Complete interval computation for depth 15, residue 9188. -/
theorem bounds_15_9188 : exactInterval 15 9188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9188 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9188) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9188 : oddCount 9188 15 = 7 ∧ acceleratedOrbit 15 9188 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9188 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9188) = 3 ^ 7 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9188.1, data_15_9188.2]

/-- Complete interval computation for depth 15, residue 9189. -/
theorem bounds_15_9189 : exactInterval 15 9189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9189 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9189) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9189 : oddCount 9189 15 = 7 ∧ acceleratedOrbit 15 9189 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9189 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9189) = 3 ^ 7 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9189.1, data_15_9189.2]

/-- Complete interval computation for depth 15, residue 9190. -/
theorem bounds_15_9190 : exactInterval 15 9190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9190 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9190) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9190 : oddCount 9190 15 = 7 ∧ acceleratedOrbit 15 9190 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9190 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9190) = 3 ^ 7 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9190.1, data_15_9190.2]

/-- Complete interval computation for depth 15, residue 9191. -/
theorem bounds_15_9191 : exactInterval 15 9191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9191 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9191) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9191 : oddCount 9191 15 = 7 ∧ acceleratedOrbit 15 9191 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9191 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9191) = 3 ^ 7 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9191.1, data_15_9191.2]

/-- Complete interval computation for depth 15, residue 9192. -/
theorem bounds_15_9192 : exactInterval 15 9192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9192 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9192) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9192 : oddCount 9192 15 = 6 ∧ acceleratedOrbit 15 9192 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9192 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9192) = 3 ^ 6 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9192.1, data_15_9192.2]

/-- Complete interval computation for depth 15, residue 9193. -/
theorem bounds_15_9193 : exactInterval 15 9193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9193 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9193) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9193 : oddCount 9193 15 = 11 ∧ acceleratedOrbit 15 9193 = 49709 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9193 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9193) = 3 ^ 11 * m + 49709 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9193.1, data_15_9193.2]

/-- Complete interval computation for depth 15, residue 9194. -/
theorem bounds_15_9194 : exactInterval 15 9194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9194 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9194) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9194 : oddCount 9194 15 = 6 ∧ acceleratedOrbit 15 9194 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9194 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9194) = 3 ^ 6 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9194.1, data_15_9194.2]

/-- Complete interval computation for depth 15, residue 9195. -/
theorem bounds_15_9195 : exactInterval 15 9195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9195 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9195) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9195 : oddCount 9195 15 = 9 ∧ acceleratedOrbit 15 9195 = 5525 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9195 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9195) = 3 ^ 9 * m + 5525 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9195.1, data_15_9195.2]

/-- Complete interval computation for depth 15, residue 9196. -/
theorem bounds_15_9196 : exactInterval 15 9196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9196 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9196) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9196 : oddCount 9196 15 = 9 ∧ acceleratedOrbit 15 9196 = 5528 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9196 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9196) = 3 ^ 9 * m + 5528 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9196.1, data_15_9196.2]

/-- Complete interval computation for depth 15, residue 9197. -/
theorem bounds_15_9197 : exactInterval 15 9197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9197 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9197) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9197 : oddCount 9197 15 = 9 ∧ acceleratedOrbit 15 9197 = 5528 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9197 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9197) = 3 ^ 9 * m + 5528 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9197.1, data_15_9197.2]

/-- Complete interval computation for depth 15, residue 9198. -/
theorem bounds_15_9198 : exactInterval 15 9198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9198 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9198) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9198 : oddCount 9198 15 = 9 ∧ acceleratedOrbit 15 9198 = 5528 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9198 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9198) = 3 ^ 9 * m + 5528 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9198.1, data_15_9198.2]

/-- Complete interval computation for depth 15, residue 9199. -/
theorem bounds_15_9199 : exactInterval 15 9199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9199 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9199) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9199 : oddCount 9199 15 = 10 ∧ acceleratedOrbit 15 9199 = 16580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9199 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9199) = 3 ^ 10 * m + 16580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9199.1, data_15_9199.2]

/-- Complete interval computation for depth 15, residue 9200. -/
theorem bounds_15_9200 : exactInterval 15 9200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9200 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9200) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9200 : oddCount 9200 15 = 6 ∧ acceleratedOrbit 15 9200 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9200 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9200) = 3 ^ 6 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9200.1, data_15_9200.2]

/-- Complete interval computation for depth 15, residue 9201. -/
theorem bounds_15_9201 : exactInterval 15 9201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9201 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9201) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9201 : oddCount 9201 15 = 6 ∧ acceleratedOrbit 15 9201 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9201 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9201) = 3 ^ 6 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9201.1, data_15_9201.2]

/-- Complete interval computation for depth 15, residue 9202. -/
theorem bounds_15_9202 : exactInterval 15 9202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9202 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9202) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9202 : oddCount 9202 15 = 8 ∧ acceleratedOrbit 15 9202 = 1844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9202 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9202) = 3 ^ 8 * m + 1844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9202.1, data_15_9202.2]

/-- Complete interval computation for depth 15, residue 9203. -/
theorem bounds_15_9203 : exactInterval 15 9203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9203 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9203) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9203 : oddCount 9203 15 = 8 ∧ acceleratedOrbit 15 9203 = 1844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9203 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9203) = 3 ^ 8 * m + 1844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9203.1, data_15_9203.2]

/-- Complete interval computation for depth 15, residue 9204. -/
theorem bounds_15_9204 : exactInterval 15 9204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9204 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9204) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9204 : oddCount 9204 15 = 6 ∧ acceleratedOrbit 15 9204 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9204 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9204) = 3 ^ 6 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9204.1, data_15_9204.2]

/-- Complete interval computation for depth 15, residue 9205. -/
theorem bounds_15_9205 : exactInterval 15 9205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9205 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9205) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9205 : oddCount 9205 15 = 6 ∧ acceleratedOrbit 15 9205 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9205 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9205) = 3 ^ 6 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9205.1, data_15_9205.2]

/-- Complete interval computation for depth 15, residue 9206. -/
theorem bounds_15_9206 : exactInterval 15 9206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9206 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9206) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9206 : oddCount 9206 15 = 9 ∧ acceleratedOrbit 15 9206 = 5534 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9206 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9206) = 3 ^ 9 * m + 5534 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9206.1, data_15_9206.2]

end Collatz.Research.PassageAtlas.Batch0281
