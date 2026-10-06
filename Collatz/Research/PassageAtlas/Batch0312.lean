import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0312

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 10190. -/
theorem bounds_15_10190 : exactInterval 15 10190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10190 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10190) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10190 : oddCount 10190 15 = 8 ∧ acceleratedOrbit 15 10190 = 2042 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10190 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10190) = 3 ^ 8 * m + 2042 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10190.1, data_15_10190.2]

/-- Complete interval computation for depth 15, residue 10191. -/
theorem bounds_15_10191 : exactInterval 15 10191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10191 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10191) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10191 : oddCount 10191 15 = 8 ∧ acceleratedOrbit 15 10191 = 2042 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10191 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10191) = 3 ^ 8 * m + 2042 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10191.1, data_15_10191.2]

/-- Complete interval computation for depth 15, residue 10192. -/
theorem bounds_15_10192 : exactInterval 15 10192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10192 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10192) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10192 : oddCount 10192 15 = 8 ∧ acceleratedOrbit 15 10192 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10192 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10192) = 3 ^ 8 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10192.1, data_15_10192.2]

/-- Complete interval computation for depth 15, residue 10193. -/
theorem bounds_15_10193 : exactInterval 15 10193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10193 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10193) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10193 : oddCount 10193 15 = 6 ∧ acceleratedOrbit 15 10193 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10193 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10193) = 3 ^ 6 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10193.1, data_15_10193.2]

/-- Complete interval computation for depth 15, residue 10194. -/
theorem bounds_15_10194 : exactInterval 15 10194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10194 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10194) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10194 : oddCount 10194 15 = 10 ∧ acceleratedOrbit 15 10194 = 18377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10194 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10194) = 3 ^ 10 * m + 18377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10194.1, data_15_10194.2]

/-- Complete interval computation for depth 15, residue 10195. -/
theorem bounds_15_10195 : exactInterval 15 10195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10195 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10195) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10195 : oddCount 10195 15 = 10 ∧ acceleratedOrbit 15 10195 = 18377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10195 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10195) = 3 ^ 10 * m + 18377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10195.1, data_15_10195.2]

/-- Complete interval computation for depth 15, residue 10196. -/
theorem bounds_15_10196 : exactInterval 15 10196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10196 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10196) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10196 : oddCount 10196 15 = 8 ∧ acceleratedOrbit 15 10196 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10196 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10196) = 3 ^ 8 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10196.1, data_15_10196.2]

/-- Complete interval computation for depth 15, residue 10197. -/
theorem bounds_15_10197 : exactInterval 15 10197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10197 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10197) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10197 : oddCount 10197 15 = 8 ∧ acceleratedOrbit 15 10197 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10197 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10197) = 3 ^ 8 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10197.1, data_15_10197.2]

/-- Complete interval computation for depth 15, residue 10198. -/
theorem bounds_15_10198 : exactInterval 15 10198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10198 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10198) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10198 : oddCount 10198 15 = 10 ∧ acceleratedOrbit 15 10198 = 18386 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10198 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10198) = 3 ^ 10 * m + 18386 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10198.1, data_15_10198.2]

/-- Complete interval computation for depth 15, residue 10199. -/
theorem bounds_15_10199 : exactInterval 15 10199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10199 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10199) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10199 : oddCount 10199 15 = 10 ∧ acceleratedOrbit 15 10199 = 18386 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10199 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10199) = 3 ^ 10 * m + 18386 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10199.1, data_15_10199.2]

/-- Complete interval computation for depth 15, residue 10200. -/
theorem bounds_15_10200 : exactInterval 15 10200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10200 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10200) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10200 : oddCount 10200 15 = 8 ∧ acceleratedOrbit 15 10200 = 2045 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10200 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10200) = 3 ^ 8 * m + 2045 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10200.1, data_15_10200.2]

/-- Complete interval computation for depth 15, residue 10201. -/
theorem bounds_15_10201 : exactInterval 15 10201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10201 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10201) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10201 : oddCount 10201 15 = 5 ∧ acceleratedOrbit 15 10201 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10201 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10201) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10201.1, data_15_10201.2]

/-- Complete interval computation for depth 15, residue 10202. -/
theorem bounds_15_10202 : exactInterval 15 10202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10202 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10202) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10202 : oddCount 10202 15 = 8 ∧ acceleratedOrbit 15 10202 = 2045 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10202 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10202) = 3 ^ 8 * m + 2045 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10202.1, data_15_10202.2]

/-- Complete interval computation for depth 15, residue 10203. -/
theorem bounds_15_10203 : exactInterval 15 10203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10203 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10203) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10203 : oddCount 10203 15 = 9 ∧ acceleratedOrbit 15 10203 = 6131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10203 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10203) = 3 ^ 9 * m + 6131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10203.1, data_15_10203.2]

/-- Complete interval computation for depth 15, residue 10204. -/
theorem bounds_15_10204 : exactInterval 15 10204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10204 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10204) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10204 : oddCount 10204 15 = 8 ∧ acceleratedOrbit 15 10204 = 2045 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10204 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10204) = 3 ^ 8 * m + 2045 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10204.1, data_15_10204.2]

/-- Complete interval computation for depth 15, residue 10205. -/
theorem bounds_15_10205 : exactInterval 15 10205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10205 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10205) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10205 : oddCount 10205 15 = 8 ∧ acceleratedOrbit 15 10205 = 2045 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10205 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10205) = 3 ^ 8 * m + 2045 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10205.1, data_15_10205.2]

/-- Complete interval computation for depth 15, residue 10206. -/
theorem bounds_15_10206 : exactInterval 15 10206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10206 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10206) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10206 : oddCount 10206 15 = 8 ∧ acceleratedOrbit 15 10206 = 2044 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10206 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10206) = 3 ^ 8 * m + 2044 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10206.1, data_15_10206.2]

/-- Complete interval computation for depth 15, residue 10207. -/
theorem bounds_15_10207 : exactInterval 15 10207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10207 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10207) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10207 : oddCount 10207 15 = 8 ∧ acceleratedOrbit 15 10207 = 2044 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10207 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10207) = 3 ^ 8 * m + 2044 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10207.1, data_15_10207.2]

/-- Complete interval computation for depth 15, residue 10208. -/
theorem bounds_15_10208 : exactInterval 15 10208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10208 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10208) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10208 : oddCount 10208 15 = 8 ∧ acceleratedOrbit 15 10208 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10208 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10208) = 3 ^ 8 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10208.1, data_15_10208.2]

/-- Complete interval computation for depth 15, residue 10209. -/
theorem bounds_15_10209 : exactInterval 15 10209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10209 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10209) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10209 : oddCount 10209 15 = 9 ∧ acceleratedOrbit 15 10209 = 6134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10209 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10209) = 3 ^ 9 * m + 6134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10209.1, data_15_10209.2]

/-- Complete interval computation for depth 15, residue 10210. -/
theorem bounds_15_10210 : exactInterval 15 10210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10210 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10210) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10210 : oddCount 10210 15 = 8 ∧ acceleratedOrbit 15 10210 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10210 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10210) = 3 ^ 8 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10210.1, data_15_10210.2]

/-- Complete interval computation for depth 15, residue 10211. -/
theorem bounds_15_10211 : exactInterval 15 10211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10211 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10211) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10211 : oddCount 10211 15 = 8 ∧ acceleratedOrbit 15 10211 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10211 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10211) = 3 ^ 8 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10211.1, data_15_10211.2]

/-- Complete interval computation for depth 15, residue 10212. -/
theorem bounds_15_10212 : exactInterval 15 10212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10212 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10212) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10212 : oddCount 10212 15 = 8 ∧ acceleratedOrbit 15 10212 = 2047 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10212 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10212) = 3 ^ 8 * m + 2047 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10212.1, data_15_10212.2]

/-- Complete interval computation for depth 15, residue 10213. -/
theorem bounds_15_10213 : exactInterval 15 10213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10213 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10213) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10213 : oddCount 10213 15 = 8 ∧ acceleratedOrbit 15 10213 = 2047 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10213 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10213) = 3 ^ 8 * m + 2047 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10213.1, data_15_10213.2]

/-- Complete interval computation for depth 15, residue 10214. -/
theorem bounds_15_10214 : exactInterval 15 10214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10214 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10214) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10214 : oddCount 10214 15 = 8 ∧ acceleratedOrbit 15 10214 = 2047 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10214 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10214) = 3 ^ 8 * m + 2047 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10214.1, data_15_10214.2]

/-- Complete interval computation for depth 15, residue 10215. -/
theorem bounds_15_10215 : exactInterval 15 10215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10215 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10215) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10215 : oddCount 10215 15 = 10 ∧ acceleratedOrbit 15 10215 = 18413 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10215 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10215) = 3 ^ 10 * m + 18413 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10215.1, data_15_10215.2]

/-- Complete interval computation for depth 15, residue 10216. -/
theorem bounds_15_10216 : exactInterval 15 10216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10216 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10216) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10216 : oddCount 10216 15 = 8 ∧ acceleratedOrbit 15 10216 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10216 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10216) = 3 ^ 8 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10216.1, data_15_10216.2]

/-- Complete interval computation for depth 15, residue 10217. -/
theorem bounds_15_10217 : exactInterval 15 10217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10217 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10217) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10217 : oddCount 10217 15 = 10 ∧ acceleratedOrbit 15 10217 = 18415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10217 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10217) = 3 ^ 10 * m + 18415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10217.1, data_15_10217.2]

/-- Complete interval computation for depth 15, residue 10218. -/
theorem bounds_15_10218 : exactInterval 15 10218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10218 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10218) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10218 : oddCount 10218 15 = 8 ∧ acceleratedOrbit 15 10218 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10218 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10218) = 3 ^ 8 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10218.1, data_15_10218.2]

/-- Complete interval computation for depth 15, residue 10219. -/
theorem bounds_15_10219 : exactInterval 15 10219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10219 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10219) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10219 : oddCount 10219 15 = 9 ∧ acceleratedOrbit 15 10219 = 6140 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10219 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10219) = 3 ^ 9 * m + 6140 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10219.1, data_15_10219.2]

/-- Complete interval computation for depth 15, residue 10220. -/
theorem bounds_15_10220 : exactInterval 15 10220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10220 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10220) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10220 : oddCount 10220 15 = 7 ∧ acceleratedOrbit 15 10220 = 683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10220 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10220) = 3 ^ 7 * m + 683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10220.1, data_15_10220.2]

/-- Complete interval computation for depth 15, residue 10221. -/
theorem bounds_15_10221 : exactInterval 15 10221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10221 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10221) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10221 : oddCount 10221 15 = 7 ∧ acceleratedOrbit 15 10221 = 683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10221 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10221) = 3 ^ 7 * m + 683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10221.1, data_15_10221.2]

/-- Complete interval computation for depth 15, residue 10222. -/
theorem bounds_15_10222 : exactInterval 15 10222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10222 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10222) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10222 : oddCount 10222 15 = 7 ∧ acceleratedOrbit 15 10222 = 683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10222 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10222) = 3 ^ 7 * m + 683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10222.1, data_15_10222.2]

end Collatz.Research.PassageAtlas.Batch0312
