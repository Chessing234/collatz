import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0892

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 29196. -/
theorem bounds_15_29196 : exactInterval 15 29196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29196 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29196) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29196 : oddCount 29196 15 = 5 ∧ acceleratedOrbit 15 29196 = 217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29196 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29196) = 3 ^ 5 * m + 217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29196.1, data_15_29196.2]

/-- Complete interval computation for depth 15, residue 29197. -/
theorem bounds_15_29197 : exactInterval 15 29197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29197 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29197) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29197 : oddCount 29197 15 = 5 ∧ acceleratedOrbit 15 29197 = 217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29197 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29197) = 3 ^ 5 * m + 217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29197.1, data_15_29197.2]

/-- Complete interval computation for depth 15, residue 29198. -/
theorem bounds_15_29198 : exactInterval 15 29198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29198 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29198) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29198 : oddCount 29198 15 = 7 ∧ acceleratedOrbit 15 29198 = 1949 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29198 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29198) = 3 ^ 7 * m + 1949 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29198.1, data_15_29198.2]

/-- Complete interval computation for depth 15, residue 29199. -/
theorem bounds_15_29199 : exactInterval 15 29199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29199 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29199) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29199 : oddCount 29199 15 = 7 ∧ acceleratedOrbit 15 29199 = 1949 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29199 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29199) = 3 ^ 7 * m + 1949 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29199.1, data_15_29199.2]

/-- Complete interval computation for depth 15, residue 29200. -/
theorem bounds_15_29200 : exactInterval 15 29200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29200 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29200) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29200 : oddCount 29200 15 = 5 ∧ acceleratedOrbit 15 29200 = 217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29200 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29200) = 3 ^ 5 * m + 217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29200.1, data_15_29200.2]

/-- Complete interval computation for depth 15, residue 29201. -/
theorem bounds_15_29201 : exactInterval 15 29201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29201 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29201) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29201 : oddCount 29201 15 = 5 ∧ acceleratedOrbit 15 29201 = 217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29201 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29201) = 3 ^ 5 * m + 217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29201.1, data_15_29201.2]

/-- Complete interval computation for depth 15, residue 29202. -/
theorem bounds_15_29202 : exactInterval 15 29202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29202 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29202) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29202 : oddCount 29202 15 = 8 ∧ acceleratedOrbit 15 29202 = 5849 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29202 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29202) = 3 ^ 8 * m + 5849 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29202.1, data_15_29202.2]

/-- Complete interval computation for depth 15, residue 29203. -/
theorem bounds_15_29203 : exactInterval 15 29203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29203 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29203) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29203 : oddCount 29203 15 = 8 ∧ acceleratedOrbit 15 29203 = 5849 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29203 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29203) = 3 ^ 8 * m + 5849 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29203.1, data_15_29203.2]

/-- Complete interval computation for depth 15, residue 29204. -/
theorem bounds_15_29204 : exactInterval 15 29204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29204 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29204) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29204 : oddCount 29204 15 = 5 ∧ acceleratedOrbit 15 29204 = 217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29204 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29204) = 3 ^ 5 * m + 217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29204.1, data_15_29204.2]

/-- Complete interval computation for depth 15, residue 29205. -/
theorem bounds_15_29205 : exactInterval 15 29205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29205 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29205) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29205 : oddCount 29205 15 = 5 ∧ acceleratedOrbit 15 29205 = 217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29205 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29205) = 3 ^ 5 * m + 217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29205.1, data_15_29205.2]

/-- Complete interval computation for depth 15, residue 29206. -/
theorem bounds_15_29206 : exactInterval 15 29206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29206 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29206) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29206 : oddCount 29206 15 = 6 ∧ acceleratedOrbit 15 29206 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29206 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29206) = 3 ^ 6 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29206.1, data_15_29206.2]

/-- Complete interval computation for depth 15, residue 29207. -/
theorem bounds_15_29207 : exactInterval 15 29207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29207 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29207) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29207 : oddCount 29207 15 = 6 ∧ acceleratedOrbit 15 29207 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29207 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29207) = 3 ^ 6 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29207.1, data_15_29207.2]

/-- Complete interval computation for depth 15, residue 29208. -/
theorem bounds_15_29208 : exactInterval 15 29208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29208 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29208) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29208 : oddCount 29208 15 = 5 ∧ acceleratedOrbit 15 29208 = 217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29208 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29208) = 3 ^ 5 * m + 217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29208.1, data_15_29208.2]

/-- Complete interval computation for depth 15, residue 29209. -/
theorem bounds_15_29209 : exactInterval 15 29209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29209 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29209) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29209 : oddCount 29209 15 = 6 ∧ acceleratedOrbit 15 29209 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29209 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29209) = 3 ^ 6 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29209.1, data_15_29209.2]

/-- Complete interval computation for depth 15, residue 29210. -/
theorem bounds_15_29210 : exactInterval 15 29210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29210 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29210) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29210 : oddCount 29210 15 = 5 ∧ acceleratedOrbit 15 29210 = 217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29210 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29210) = 3 ^ 5 * m + 217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29210.1, data_15_29210.2]

/-- Complete interval computation for depth 15, residue 29211. -/
theorem bounds_15_29211 : exactInterval 15 29211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29211 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29211) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29211 : oddCount 29211 15 = 10 ∧ acceleratedOrbit 15 29211 = 52643 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29211 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29211) = 3 ^ 10 * m + 52643 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29211.1, data_15_29211.2]

/-- Complete interval computation for depth 15, residue 29212. -/
theorem bounds_15_29212 : exactInterval 15 29212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29212 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29212) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29212 : oddCount 29212 15 = 8 ∧ acceleratedOrbit 15 29212 = 5852 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29212 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29212) = 3 ^ 8 * m + 5852 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29212.1, data_15_29212.2]

/-- Complete interval computation for depth 15, residue 29213. -/
theorem bounds_15_29213 : exactInterval 15 29213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29213 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29213) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29213 : oddCount 29213 15 = 8 ∧ acceleratedOrbit 15 29213 = 5852 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29213 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29213) = 3 ^ 8 * m + 5852 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29213.1, data_15_29213.2]

/-- Complete interval computation for depth 15, residue 29214. -/
theorem bounds_15_29214 : exactInterval 15 29214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29214 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29214) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29214 : oddCount 29214 15 = 8 ∧ acceleratedOrbit 15 29214 = 5852 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29214 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29214) = 3 ^ 8 * m + 5852 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29214.1, data_15_29214.2]

/-- Complete interval computation for depth 15, residue 29215. -/
theorem bounds_15_29215 : exactInterval 15 29215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29215 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29215) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29215 : oddCount 29215 15 = 11 ∧ acceleratedOrbit 15 29215 = 157949 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29215 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29215) = 3 ^ 11 * m + 157949 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29215.1, data_15_29215.2]

/-- Complete interval computation for depth 15, residue 29216. -/
theorem bounds_15_29216 : exactInterval 15 29216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29216 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29216) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29216 : oddCount 29216 15 = 5 ∧ acceleratedOrbit 15 29216 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29216 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29216) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29216.1, data_15_29216.2]

/-- Complete interval computation for depth 15, residue 29217. -/
theorem bounds_15_29217 : exactInterval 15 29217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29217 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29217) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29217 : oddCount 29217 15 = 8 ∧ acceleratedOrbit 15 29217 = 5852 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29217 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29217) = 3 ^ 8 * m + 5852 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29217.1, data_15_29217.2]

/-- Complete interval computation for depth 15, residue 29218. -/
theorem bounds_15_29218 : exactInterval 15 29218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29218 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29218) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29218 : oddCount 29218 15 = 5 ∧ acceleratedOrbit 15 29218 = 217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29218 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29218) = 3 ^ 5 * m + 217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29218.1, data_15_29218.2]

/-- Complete interval computation for depth 15, residue 29219. -/
theorem bounds_15_29219 : exactInterval 15 29219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29219 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29219) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29219 : oddCount 29219 15 = 5 ∧ acceleratedOrbit 15 29219 = 217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29219 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29219) = 3 ^ 5 * m + 217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29219.1, data_15_29219.2]

/-- Complete interval computation for depth 15, residue 29220. -/
theorem bounds_15_29220 : exactInterval 15 29220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29220 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29220) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29220 : oddCount 29220 15 = 10 ∧ acceleratedOrbit 15 29220 = 52670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29220 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29220) = 3 ^ 10 * m + 52670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29220.1, data_15_29220.2]

/-- Complete interval computation for depth 15, residue 29221. -/
theorem bounds_15_29221 : exactInterval 15 29221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29221 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29221) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29221 : oddCount 29221 15 = 10 ∧ acceleratedOrbit 15 29221 = 52670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29221 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29221) = 3 ^ 10 * m + 52670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29221.1, data_15_29221.2]

/-- Complete interval computation for depth 15, residue 29222. -/
theorem bounds_15_29222 : exactInterval 15 29222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29222 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29222) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29222 : oddCount 29222 15 = 10 ∧ acceleratedOrbit 15 29222 = 52670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29222 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29222) = 3 ^ 10 * m + 52670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29222.1, data_15_29222.2]

/-- Complete interval computation for depth 15, residue 29223. -/
theorem bounds_15_29223 : exactInterval 15 29223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29223 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29223) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29223 : oddCount 29223 15 = 8 ∧ acceleratedOrbit 15 29223 = 5852 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29223 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29223) = 3 ^ 8 * m + 5852 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29223.1, data_15_29223.2]

/-- Complete interval computation for depth 15, residue 29224. -/
theorem bounds_15_29224 : exactInterval 15 29224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29224 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29224) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29224 : oddCount 29224 15 = 5 ∧ acceleratedOrbit 15 29224 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29224 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29224) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29224.1, data_15_29224.2]

/-- Complete interval computation for depth 15, residue 29225. -/
theorem bounds_15_29225 : exactInterval 15 29225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29225 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29225) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29225 : oddCount 29225 15 = 12 ∧ acceleratedOrbit 15 29225 = 474011 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29225 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29225) = 3 ^ 12 * m + 474011 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29225.1, data_15_29225.2]

/-- Complete interval computation for depth 15, residue 29226. -/
theorem bounds_15_29226 : exactInterval 15 29226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29226 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29226) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29226 : oddCount 29226 15 = 5 ∧ acceleratedOrbit 15 29226 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29226 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29226) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29226.1, data_15_29226.2]

/-- Complete interval computation for depth 15, residue 29227. -/
theorem bounds_15_29227 : exactInterval 15 29227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29227 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29227) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29227 : oddCount 29227 15 = 5 ∧ acceleratedOrbit 15 29227 = 217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29227 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29227) = 3 ^ 5 * m + 217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29227.1, data_15_29227.2]

/-- Complete interval computation for depth 15, residue 29228. -/
theorem bounds_15_29228 : exactInterval 15 29228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29228 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29228) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29228 : oddCount 29228 15 = 7 ∧ acceleratedOrbit 15 29228 = 1952 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29228 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29228) = 3 ^ 7 * m + 1952 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29228.1, data_15_29228.2]

end Collatz.Research.PassageAtlas.Batch0892
