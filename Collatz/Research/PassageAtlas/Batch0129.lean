import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0129

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 4194. -/
theorem bounds_15_4194 : exactInterval 15 4194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4194 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4194) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4194 : oddCount 4194 15 = 7 ∧ acceleratedOrbit 15 4194 = 281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4194 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4194) = 3 ^ 7 * m + 281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4194.1, data_15_4194.2]

/-- Complete interval computation for depth 15, residue 4195. -/
theorem bounds_15_4195 : exactInterval 15 4195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4195 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4195) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4195 : oddCount 4195 15 = 7 ∧ acceleratedOrbit 15 4195 = 281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4195 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4195) = 3 ^ 7 * m + 281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4195.1, data_15_4195.2]

/-- Complete interval computation for depth 15, residue 4196. -/
theorem bounds_15_4196 : exactInterval 15 4196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4196 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4196) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4196 : oddCount 4196 15 = 7 ∧ acceleratedOrbit 15 4196 = 281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4196 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4196) = 3 ^ 7 * m + 281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4196.1, data_15_4196.2]

/-- Complete interval computation for depth 15, residue 4197. -/
theorem bounds_15_4197 : exactInterval 15 4197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4197 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4197) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4197 : oddCount 4197 15 = 7 ∧ acceleratedOrbit 15 4197 = 281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4197 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4197) = 3 ^ 7 * m + 281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4197.1, data_15_4197.2]

/-- Complete interval computation for depth 15, residue 4198. -/
theorem bounds_15_4198 : exactInterval 15 4198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4198 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4198) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4198 : oddCount 4198 15 = 7 ∧ acceleratedOrbit 15 4198 = 281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4198 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4198) = 3 ^ 7 * m + 281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4198.1, data_15_4198.2]

/-- Complete interval computation for depth 15, residue 4199. -/
theorem bounds_15_4199 : exactInterval 15 4199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4199 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4199) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4199 : oddCount 4199 15 = 8 ∧ acceleratedOrbit 15 4199 = 841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4199 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4199) = 3 ^ 8 * m + 841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4199.1, data_15_4199.2]

/-- Complete interval computation for depth 15, residue 4200. -/
theorem bounds_15_4200 : exactInterval 15 4200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4200 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4200) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4200 : oddCount 4200 15 = 4 ∧ acceleratedOrbit 15 4200 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4200 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4200) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4200.1, data_15_4200.2]

/-- Complete interval computation for depth 15, residue 4201. -/
theorem bounds_15_4201 : exactInterval 15 4201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4201 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4201) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4201 : oddCount 4201 15 = 7 ∧ acceleratedOrbit 15 4201 = 281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4201 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4201) = 3 ^ 7 * m + 281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4201.1, data_15_4201.2]

/-- Complete interval computation for depth 15, residue 4202. -/
theorem bounds_15_4202 : exactInterval 15 4202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4202 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4202) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4202 : oddCount 4202 15 = 4 ∧ acceleratedOrbit 15 4202 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4202 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4202) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4202.1, data_15_4202.2]

/-- Complete interval computation for depth 15, residue 4203. -/
theorem bounds_15_4203 : exactInterval 15 4203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4203 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4203) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4203 : oddCount 4203 15 = 8 ∧ acceleratedOrbit 15 4203 = 842 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4203 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4203) = 3 ^ 8 * m + 842 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4203.1, data_15_4203.2]

/-- Complete interval computation for depth 15, residue 4204. -/
theorem bounds_15_4204 : exactInterval 15 4204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4204 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4204) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4204 : oddCount 4204 15 = 11 ∧ acceleratedOrbit 15 4204 = 22760 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4204 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4204) = 3 ^ 11 * m + 22760 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4204.1, data_15_4204.2]

/-- Complete interval computation for depth 15, residue 4205. -/
theorem bounds_15_4205 : exactInterval 15 4205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4205 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4205) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4205 : oddCount 4205 15 = 11 ∧ acceleratedOrbit 15 4205 = 22760 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4205 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4205) = 3 ^ 11 * m + 22760 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4205.1, data_15_4205.2]

/-- Complete interval computation for depth 15, residue 4206. -/
theorem bounds_15_4206 : exactInterval 15 4206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4206 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4206) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4206 : oddCount 4206 15 = 11 ∧ acceleratedOrbit 15 4206 = 22760 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4206 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4206) = 3 ^ 11 * m + 22760 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4206.1, data_15_4206.2]

/-- Complete interval computation for depth 15, residue 4207. -/
theorem bounds_15_4207 : exactInterval 15 4207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4207 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4207) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4207 : oddCount 4207 15 = 11 ∧ acceleratedOrbit 15 4207 = 22751 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4207 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4207) = 3 ^ 11 * m + 22751 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4207.1, data_15_4207.2]

/-- Complete interval computation for depth 15, residue 4208. -/
theorem bounds_15_4208 : exactInterval 15 4208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4208 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4208) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4208 : oddCount 4208 15 = 7 ∧ acceleratedOrbit 15 4208 = 283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4208 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4208) = 3 ^ 7 * m + 283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4208.1, data_15_4208.2]

/-- Complete interval computation for depth 15, residue 4209. -/
theorem bounds_15_4209 : exactInterval 15 4209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4209 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4209) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4209 : oddCount 4209 15 = 4 ∧ acceleratedOrbit 15 4209 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4209 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4209) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4209.1, data_15_4209.2]

/-- Complete interval computation for depth 15, residue 4210. -/
theorem bounds_15_4210 : exactInterval 15 4210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4210 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4210) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4210 : oddCount 4210 15 = 6 ∧ acceleratedOrbit 15 4210 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4210 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4210) = 3 ^ 6 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4210.1, data_15_4210.2]

/-- Complete interval computation for depth 15, residue 4211. -/
theorem bounds_15_4211 : exactInterval 15 4211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4211 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4211) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4211 : oddCount 4211 15 = 6 ∧ acceleratedOrbit 15 4211 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4211 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4211) = 3 ^ 6 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4211.1, data_15_4211.2]

/-- Complete interval computation for depth 15, residue 4212. -/
theorem bounds_15_4212 : exactInterval 15 4212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4212 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4212) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4212 : oddCount 4212 15 = 7 ∧ acceleratedOrbit 15 4212 = 283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4212 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4212) = 3 ^ 7 * m + 283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4212.1, data_15_4212.2]

/-- Complete interval computation for depth 15, residue 4213. -/
theorem bounds_15_4213 : exactInterval 15 4213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4213 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4213) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4213 : oddCount 4213 15 = 7 ∧ acceleratedOrbit 15 4213 = 283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4213 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4213) = 3 ^ 7 * m + 283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4213.1, data_15_4213.2]

/-- Complete interval computation for depth 15, residue 4214. -/
theorem bounds_15_4214 : exactInterval 15 4214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4214 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4214) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4214 : oddCount 4214 15 = 9 ∧ acceleratedOrbit 15 4214 = 2537 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4214 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4214) = 3 ^ 9 * m + 2537 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4214.1, data_15_4214.2]

/-- Complete interval computation for depth 15, residue 4215. -/
theorem bounds_15_4215 : exactInterval 15 4215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4215 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4215) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4215 : oddCount 4215 15 = 9 ∧ acceleratedOrbit 15 4215 = 2537 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4215 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4215) = 3 ^ 9 * m + 2537 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4215.1, data_15_4215.2]

/-- Complete interval computation for depth 15, residue 4216. -/
theorem bounds_15_4216 : exactInterval 15 4216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4216 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4216) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4216 : oddCount 4216 15 = 7 ∧ acceleratedOrbit 15 4216 = 283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4216 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4216) = 3 ^ 7 * m + 283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4216.1, data_15_4216.2]

/-- Complete interval computation for depth 15, residue 4217. -/
theorem bounds_15_4217 : exactInterval 15 4217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4217 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4217) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4217 : oddCount 4217 15 = 10 ∧ acceleratedOrbit 15 4217 = 7604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4217 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4217) = 3 ^ 10 * m + 7604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4217.1, data_15_4217.2]

/-- Complete interval computation for depth 15, residue 4218. -/
theorem bounds_15_4218 : exactInterval 15 4218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4218 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4218) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4218 : oddCount 4218 15 = 7 ∧ acceleratedOrbit 15 4218 = 283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4218 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4218) = 3 ^ 7 * m + 283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4218.1, data_15_4218.2]

/-- Complete interval computation for depth 15, residue 4219. -/
theorem bounds_15_4219 : exactInterval 15 4219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4219 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4219) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4219 : oddCount 4219 15 = 9 ∧ acceleratedOrbit 15 4219 = 2537 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4219 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4219) = 3 ^ 9 * m + 2537 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4219.1, data_15_4219.2]

/-- Complete interval computation for depth 15, residue 4220. -/
theorem bounds_15_4220 : exactInterval 15 4220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4220 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4220) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4220 : oddCount 4220 15 = 11 ∧ acceleratedOrbit 15 4220 = 22841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4220 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4220) = 3 ^ 11 * m + 22841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4220.1, data_15_4220.2]

/-- Complete interval computation for depth 15, residue 4221. -/
theorem bounds_15_4221 : exactInterval 15 4221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4221 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4221) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4221 : oddCount 4221 15 = 11 ∧ acceleratedOrbit 15 4221 = 22841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4221 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4221) = 3 ^ 11 * m + 22841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4221.1, data_15_4221.2]

/-- Complete interval computation for depth 15, residue 4222. -/
theorem bounds_15_4222 : exactInterval 15 4222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4222 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4222) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4222 : oddCount 4222 15 = 11 ∧ acceleratedOrbit 15 4222 = 22841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4222 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4222) = 3 ^ 11 * m + 22841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4222.1, data_15_4222.2]

/-- Complete interval computation for depth 15, residue 4223. -/
theorem bounds_15_4223 : exactInterval 15 4223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4223 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4223) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4223 : oddCount 4223 15 = 10 ∧ acceleratedOrbit 15 4223 = 7613 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4223 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4223) = 3 ^ 10 * m + 7613 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4223.1, data_15_4223.2]

/-- Complete interval computation for depth 15, residue 4224. -/
theorem bounds_15_4224 : exactInterval 15 4224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4224 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4224) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4224 : oddCount 4224 15 = 4 ∧ acceleratedOrbit 15 4224 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4224 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4224) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4224.1, data_15_4224.2]

/-- Complete interval computation for depth 15, residue 4225. -/
theorem bounds_15_4225 : exactInterval 15 4225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4225 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4225) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4225 : oddCount 4225 15 = 8 ∧ acceleratedOrbit 15 4225 = 847 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4225 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4225) = 3 ^ 8 * m + 847 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4225.1, data_15_4225.2]

/-- Complete interval computation for depth 15, residue 4226. -/
theorem bounds_15_4226 : exactInterval 15 4226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4226 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4226) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4226 : oddCount 4226 15 = 8 ∧ acceleratedOrbit 15 4226 = 850 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4226 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4226) = 3 ^ 8 * m + 850 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4226.1, data_15_4226.2]

end Collatz.Research.PassageAtlas.Batch0129
