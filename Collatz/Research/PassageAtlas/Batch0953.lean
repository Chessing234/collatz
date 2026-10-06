import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0953

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 31195. -/
theorem bounds_15_31195 : exactInterval 15 31195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31195 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31195) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31195 : oddCount 31195 15 = 8 ∧ acceleratedOrbit 15 31195 = 6247 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31195 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31195) = 3 ^ 8 * m + 6247 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31195.1, data_15_31195.2]

/-- Complete interval computation for depth 15, residue 31196. -/
theorem bounds_15_31196 : exactInterval 15 31196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31196 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31196) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31196 : oddCount 31196 15 = 6 ∧ acceleratedOrbit 15 31196 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31196 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31196) = 3 ^ 6 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31196.1, data_15_31196.2]

/-- Complete interval computation for depth 15, residue 31197. -/
theorem bounds_15_31197 : exactInterval 15 31197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31197 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31197) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31197 : oddCount 31197 15 = 6 ∧ acceleratedOrbit 15 31197 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31197 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31197) = 3 ^ 6 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31197.1, data_15_31197.2]

/-- Complete interval computation for depth 15, residue 31198. -/
theorem bounds_15_31198 : exactInterval 15 31198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31198 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31198) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31198 : oddCount 31198 15 = 10 ∧ acceleratedOrbit 15 31198 = 56224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31198 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31198) = 3 ^ 10 * m + 56224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31198.1, data_15_31198.2]

/-- Complete interval computation for depth 15, residue 31199. -/
theorem bounds_15_31199 : exactInterval 15 31199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31199 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31199) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31199 : oddCount 31199 15 = 10 ∧ acceleratedOrbit 15 31199 = 56224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31199 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31199) = 3 ^ 10 * m + 56224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31199.1, data_15_31199.2]

/-- Complete interval computation for depth 15, residue 31200. -/
theorem bounds_15_31200 : exactInterval 15 31200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31200 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31200) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31200 : oddCount 31200 15 = 6 ∧ acceleratedOrbit 15 31200 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31200 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31200) = 3 ^ 6 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31200.1, data_15_31200.2]

/-- Complete interval computation for depth 15, residue 31201. -/
theorem bounds_15_31201 : exactInterval 15 31201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31201 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31201) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31201 : oddCount 31201 15 = 8 ∧ acceleratedOrbit 15 31201 = 6248 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31201 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31201) = 3 ^ 8 * m + 6248 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31201.1, data_15_31201.2]

/-- Complete interval computation for depth 15, residue 31202. -/
theorem bounds_15_31202 : exactInterval 15 31202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31202 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31202) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31202 : oddCount 31202 15 = 6 ∧ acceleratedOrbit 15 31202 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31202 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31202) = 3 ^ 6 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31202.1, data_15_31202.2]

/-- Complete interval computation for depth 15, residue 31203. -/
theorem bounds_15_31203 : exactInterval 15 31203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31203 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31203) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31203 : oddCount 31203 15 = 6 ∧ acceleratedOrbit 15 31203 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31203 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31203) = 3 ^ 6 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31203.1, data_15_31203.2]

/-- Complete interval computation for depth 15, residue 31204. -/
theorem bounds_15_31204 : exactInterval 15 31204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31204 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31204) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31204 : oddCount 31204 15 = 8 ∧ acceleratedOrbit 15 31204 = 6250 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31204 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31204) = 3 ^ 8 * m + 6250 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31204.1, data_15_31204.2]

/-- Complete interval computation for depth 15, residue 31205. -/
theorem bounds_15_31205 : exactInterval 15 31205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31205 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31205) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31205 : oddCount 31205 15 = 8 ∧ acceleratedOrbit 15 31205 = 6250 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31205 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31205) = 3 ^ 8 * m + 6250 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31205.1, data_15_31205.2]

/-- Complete interval computation for depth 15, residue 31206. -/
theorem bounds_15_31206 : exactInterval 15 31206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31206 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31206) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31206 : oddCount 31206 15 = 8 ∧ acceleratedOrbit 15 31206 = 6250 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31206 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31206) = 3 ^ 8 * m + 6250 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31206.1, data_15_31206.2]

/-- Complete interval computation for depth 15, residue 31207. -/
theorem bounds_15_31207 : exactInterval 15 31207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31207 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31207) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31207 : oddCount 31207 15 = 10 ∧ acceleratedOrbit 15 31207 = 56240 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31207 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31207) = 3 ^ 10 * m + 56240 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31207.1, data_15_31207.2]

/-- Complete interval computation for depth 15, residue 31208. -/
theorem bounds_15_31208 : exactInterval 15 31208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31208 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31208) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31208 : oddCount 31208 15 = 6 ∧ acceleratedOrbit 15 31208 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31208 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31208) = 3 ^ 6 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31208.1, data_15_31208.2]

/-- Complete interval computation for depth 15, residue 31209. -/
theorem bounds_15_31209 : exactInterval 15 31209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31209 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31209) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31209 : oddCount 31209 15 = 9 ∧ acceleratedOrbit 15 31209 = 18748 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31209 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31209) = 3 ^ 9 * m + 18748 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31209.1, data_15_31209.2]

/-- Complete interval computation for depth 15, residue 31210. -/
theorem bounds_15_31210 : exactInterval 15 31210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31210 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31210) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31210 : oddCount 31210 15 = 6 ∧ acceleratedOrbit 15 31210 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31210 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31210) = 3 ^ 6 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31210.1, data_15_31210.2]

/-- Complete interval computation for depth 15, residue 31211. -/
theorem bounds_15_31211 : exactInterval 15 31211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31211 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31211) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31211 : oddCount 31211 15 = 9 ∧ acceleratedOrbit 15 31211 = 18749 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31211 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31211) = 3 ^ 9 * m + 18749 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31211.1, data_15_31211.2]

/-- Complete interval computation for depth 15, residue 31212. -/
theorem bounds_15_31212 : exactInterval 15 31212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31212 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31212) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31212 : oddCount 31212 15 = 6 ∧ acceleratedOrbit 15 31212 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31212 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31212) = 3 ^ 6 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31212.1, data_15_31212.2]

/-- Complete interval computation for depth 15, residue 31213. -/
theorem bounds_15_31213 : exactInterval 15 31213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31213 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31213) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31213 : oddCount 31213 15 = 6 ∧ acceleratedOrbit 15 31213 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31213 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31213) = 3 ^ 6 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31213.1, data_15_31213.2]

/-- Complete interval computation for depth 15, residue 31214. -/
theorem bounds_15_31214 : exactInterval 15 31214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31214 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31214) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31214 : oddCount 31214 15 = 6 ∧ acceleratedOrbit 15 31214 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31214 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31214) = 3 ^ 6 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31214.1, data_15_31214.2]

/-- Complete interval computation for depth 15, residue 31215. -/
theorem bounds_15_31215 : exactInterval 15 31215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31215 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31215) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31215 : oddCount 31215 15 = 12 ∧ acceleratedOrbit 15 31215 = 506276 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31215 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31215) = 3 ^ 12 * m + 506276 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31215.1, data_15_31215.2]

/-- Complete interval computation for depth 15, residue 31216. -/
theorem bounds_15_31216 : exactInterval 15 31216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31216 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31216) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31216 : oddCount 31216 15 = 8 ∧ acceleratedOrbit 15 31216 = 6254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31216 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31216) = 3 ^ 8 * m + 6254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31216.1, data_15_31216.2]

/-- Complete interval computation for depth 15, residue 31217. -/
theorem bounds_15_31217 : exactInterval 15 31217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31217 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31217) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31217 : oddCount 31217 15 = 6 ∧ acceleratedOrbit 15 31217 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31217 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31217) = 3 ^ 6 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31217.1, data_15_31217.2]

/-- Complete interval computation for depth 15, residue 31218. -/
theorem bounds_15_31218 : exactInterval 15 31218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31218 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31218) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31218 : oddCount 31218 15 = 7 ∧ acceleratedOrbit 15 31218 = 2084 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31218 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31218) = 3 ^ 7 * m + 2084 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31218.1, data_15_31218.2]

/-- Complete interval computation for depth 15, residue 31219. -/
theorem bounds_15_31219 : exactInterval 15 31219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31219 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31219) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31219 : oddCount 31219 15 = 7 ∧ acceleratedOrbit 15 31219 = 2084 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31219 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31219) = 3 ^ 7 * m + 2084 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31219.1, data_15_31219.2]

/-- Complete interval computation for depth 15, residue 31220. -/
theorem bounds_15_31220 : exactInterval 15 31220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31220 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31220) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31220 : oddCount 31220 15 = 8 ∧ acceleratedOrbit 15 31220 = 6254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31220 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31220) = 3 ^ 8 * m + 6254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31220.1, data_15_31220.2]

/-- Complete interval computation for depth 15, residue 31221. -/
theorem bounds_15_31221 : exactInterval 15 31221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31221 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31221) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31221 : oddCount 31221 15 = 8 ∧ acceleratedOrbit 15 31221 = 6254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31221 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31221) = 3 ^ 8 * m + 6254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31221.1, data_15_31221.2]

/-- Complete interval computation for depth 15, residue 31222. -/
theorem bounds_15_31222 : exactInterval 15 31222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31222 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31222) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31222 : oddCount 31222 15 = 10 ∧ acceleratedOrbit 15 31222 = 56270 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31222 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31222) = 3 ^ 10 * m + 56270 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31222.1, data_15_31222.2]

/-- Complete interval computation for depth 15, residue 31223. -/
theorem bounds_15_31223 : exactInterval 15 31223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31223 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31223) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31223 : oddCount 31223 15 = 10 ∧ acceleratedOrbit 15 31223 = 56270 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31223 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31223) = 3 ^ 10 * m + 56270 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31223.1, data_15_31223.2]

/-- Complete interval computation for depth 15, residue 31224. -/
theorem bounds_15_31224 : exactInterval 15 31224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31224 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31224) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31224 : oddCount 31224 15 = 8 ∧ acceleratedOrbit 15 31224 = 6254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31224 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31224) = 3 ^ 8 * m + 6254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31224.1, data_15_31224.2]

/-- Complete interval computation for depth 15, residue 31225. -/
theorem bounds_15_31225 : exactInterval 15 31225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31225 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31225) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31225 : oddCount 31225 15 = 9 ∧ acceleratedOrbit 15 31225 = 18758 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31225 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31225) = 3 ^ 9 * m + 18758 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31225.1, data_15_31225.2]

/-- Complete interval computation for depth 15, residue 31226. -/
theorem bounds_15_31226 : exactInterval 15 31226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31226 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31226) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31226 : oddCount 31226 15 = 8 ∧ acceleratedOrbit 15 31226 = 6254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31226 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31226) = 3 ^ 8 * m + 6254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31226.1, data_15_31226.2]

end Collatz.Research.PassageAtlas.Batch0953
