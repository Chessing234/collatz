import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0343

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 11206. -/
theorem bounds_15_11206 : exactInterval 15 11206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11206 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11206) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11206 : oddCount 11206 15 = 4 ∧ acceleratedOrbit 15 11206 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11206 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11206) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11206.1, data_15_11206.2]

/-- Complete interval computation for depth 15, residue 11207. -/
theorem bounds_15_11207 : exactInterval 15 11207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11207 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11207) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11207 : oddCount 11207 15 = 9 ∧ acceleratedOrbit 15 11207 = 6733 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11207 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11207) = 3 ^ 9 * m + 6733 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11207.1, data_15_11207.2]

/-- Complete interval computation for depth 15, residue 11208. -/
theorem bounds_15_11208 : exactInterval 15 11208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11208 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11208) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11208 : oddCount 11208 15 = 9 ∧ acceleratedOrbit 15 11208 = 6743 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11208 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11208) = 3 ^ 9 * m + 6743 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11208.1, data_15_11208.2]

/-- Complete interval computation for depth 15, residue 11209. -/
theorem bounds_15_11209 : exactInterval 15 11209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11209 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11209) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11209 : oddCount 11209 15 = 9 ∧ acceleratedOrbit 15 11209 = 6736 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11209 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11209) = 3 ^ 9 * m + 6736 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11209.1, data_15_11209.2]

/-- Complete interval computation for depth 15, residue 11210. -/
theorem bounds_15_11210 : exactInterval 15 11210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11210 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11210) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11210 : oddCount 11210 15 = 9 ∧ acceleratedOrbit 15 11210 = 6743 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11210 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11210) = 3 ^ 9 * m + 6743 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11210.1, data_15_11210.2]

/-- Complete interval computation for depth 15, residue 11211. -/
theorem bounds_15_11211 : exactInterval 15 11211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11211 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11211) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11211 : oddCount 11211 15 = 7 ∧ acceleratedOrbit 15 11211 = 749 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11211 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11211) = 3 ^ 7 * m + 749 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11211.1, data_15_11211.2]

/-- Complete interval computation for depth 15, residue 11212. -/
theorem bounds_15_11212 : exactInterval 15 11212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11212 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11212) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11212 : oddCount 11212 15 = 9 ∧ acceleratedOrbit 15 11212 = 6743 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11212 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11212) = 3 ^ 9 * m + 6743 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11212.1, data_15_11212.2]

/-- Complete interval computation for depth 15, residue 11213. -/
theorem bounds_15_11213 : exactInterval 15 11213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11213 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11213) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11213 : oddCount 11213 15 = 9 ∧ acceleratedOrbit 15 11213 = 6743 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11213 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11213) = 3 ^ 9 * m + 6743 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11213.1, data_15_11213.2]

/-- Complete interval computation for depth 15, residue 11214. -/
theorem bounds_15_11214 : exactInterval 15 11214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11214 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11214) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11214 : oddCount 11214 15 = 8 ∧ acceleratedOrbit 15 11214 = 2246 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11214 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11214) = 3 ^ 8 * m + 2246 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11214.1, data_15_11214.2]

/-- Complete interval computation for depth 15, residue 11215. -/
theorem bounds_15_11215 : exactInterval 15 11215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11215 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11215) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11215 : oddCount 11215 15 = 8 ∧ acceleratedOrbit 15 11215 = 2246 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11215 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11215) = 3 ^ 8 * m + 2246 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11215.1, data_15_11215.2]

/-- Complete interval computation for depth 15, residue 11216. -/
theorem bounds_15_11216 : exactInterval 15 11216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11216 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11216) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11216 : oddCount 11216 15 = 6 ∧ acceleratedOrbit 15 11216 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11216 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11216) = 3 ^ 6 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11216.1, data_15_11216.2]

/-- Complete interval computation for depth 15, residue 11217. -/
theorem bounds_15_11217 : exactInterval 15 11217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11217 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11217) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11217 : oddCount 11217 15 = 9 ∧ acceleratedOrbit 15 11217 = 6743 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11217 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11217) = 3 ^ 9 * m + 6743 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11217.1, data_15_11217.2]

/-- Complete interval computation for depth 15, residue 11218. -/
theorem bounds_15_11218 : exactInterval 15 11218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11218 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11218) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11218 : oddCount 11218 15 = 11 ∧ acceleratedOrbit 15 11218 = 60668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11218 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11218) = 3 ^ 11 * m + 60668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11218.1, data_15_11218.2]

/-- Complete interval computation for depth 15, residue 11219. -/
theorem bounds_15_11219 : exactInterval 15 11219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11219 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11219) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11219 : oddCount 11219 15 = 11 ∧ acceleratedOrbit 15 11219 = 60668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11219 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11219) = 3 ^ 11 * m + 60668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11219.1, data_15_11219.2]

/-- Complete interval computation for depth 15, residue 11220. -/
theorem bounds_15_11220 : exactInterval 15 11220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11220 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11220) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11220 : oddCount 11220 15 = 6 ∧ acceleratedOrbit 15 11220 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11220 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11220) = 3 ^ 6 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11220.1, data_15_11220.2]

/-- Complete interval computation for depth 15, residue 11221. -/
theorem bounds_15_11221 : exactInterval 15 11221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11221 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11221) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11221 : oddCount 11221 15 = 6 ∧ acceleratedOrbit 15 11221 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11221 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11221) = 3 ^ 6 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11221.1, data_15_11221.2]

/-- Complete interval computation for depth 15, residue 11222. -/
theorem bounds_15_11222 : exactInterval 15 11222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11222 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11222) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11222 : oddCount 11222 15 = 11 ∧ acceleratedOrbit 15 11222 = 60689 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11222 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11222) = 3 ^ 11 * m + 60689 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11222.1, data_15_11222.2]

/-- Complete interval computation for depth 15, residue 11223. -/
theorem bounds_15_11223 : exactInterval 15 11223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11223 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11223) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11223 : oddCount 11223 15 = 11 ∧ acceleratedOrbit 15 11223 = 60689 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11223 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11223) = 3 ^ 11 * m + 60689 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11223.1, data_15_11223.2]

/-- Complete interval computation for depth 15, residue 11224. -/
theorem bounds_15_11224 : exactInterval 15 11224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11224 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11224) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11224 : oddCount 11224 15 = 6 ∧ acceleratedOrbit 15 11224 = 250 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11224 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11224) = 3 ^ 6 * m + 250 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11224.1, data_15_11224.2]

/-- Complete interval computation for depth 15, residue 11225. -/
theorem bounds_15_11225 : exactInterval 15 11225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11225 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11225) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11225 : oddCount 11225 15 = 4 ∧ acceleratedOrbit 15 11225 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11225 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11225) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11225.1, data_15_11225.2]

/-- Complete interval computation for depth 15, residue 11226. -/
theorem bounds_15_11226 : exactInterval 15 11226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11226 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11226) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11226 : oddCount 11226 15 = 6 ∧ acceleratedOrbit 15 11226 = 250 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11226 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11226) = 3 ^ 6 * m + 250 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11226.1, data_15_11226.2]

/-- Complete interval computation for depth 15, residue 11227. -/
theorem bounds_15_11227 : exactInterval 15 11227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11227 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11227) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11227 : oddCount 11227 15 = 8 ∧ acceleratedOrbit 15 11227 = 2249 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11227 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11227) = 3 ^ 8 * m + 2249 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11227.1, data_15_11227.2]

/-- Complete interval computation for depth 15, residue 11228. -/
theorem bounds_15_11228 : exactInterval 15 11228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11228 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11228) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11228 : oddCount 11228 15 = 6 ∧ acceleratedOrbit 15 11228 = 250 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11228 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11228) = 3 ^ 6 * m + 250 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11228.1, data_15_11228.2]

/-- Complete interval computation for depth 15, residue 11229. -/
theorem bounds_15_11229 : exactInterval 15 11229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11229 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11229) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11229 : oddCount 11229 15 = 6 ∧ acceleratedOrbit 15 11229 = 250 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11229 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11229) = 3 ^ 6 * m + 250 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11229.1, data_15_11229.2]

/-- Complete interval computation for depth 15, residue 11230. -/
theorem bounds_15_11230 : exactInterval 15 11230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11230 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11230) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11230 : oddCount 11230 15 = 8 ∧ acceleratedOrbit 15 11230 = 2249 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11230 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11230) = 3 ^ 8 * m + 2249 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11230.1, data_15_11230.2]

/-- Complete interval computation for depth 15, residue 11231. -/
theorem bounds_15_11231 : exactInterval 15 11231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11231 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11231) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11231 : oddCount 11231 15 = 8 ∧ acceleratedOrbit 15 11231 = 2249 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11231 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11231) = 3 ^ 8 * m + 2249 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11231.1, data_15_11231.2]

/-- Complete interval computation for depth 15, residue 11232. -/
theorem bounds_15_11232 : exactInterval 15 11232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11232 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11232) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11232 : oddCount 11232 15 = 6 ∧ acceleratedOrbit 15 11232 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11232 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11232) = 3 ^ 6 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11232.1, data_15_11232.2]

/-- Complete interval computation for depth 15, residue 11233. -/
theorem bounds_15_11233 : exactInterval 15 11233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11233 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11233) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11233 : oddCount 11233 15 = 10 ∧ acceleratedOrbit 15 11233 = 20249 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11233 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11233) = 3 ^ 10 * m + 20249 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11233.1, data_15_11233.2]

/-- Complete interval computation for depth 15, residue 11234. -/
theorem bounds_15_11234 : exactInterval 15 11234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11234 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11234) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11234 : oddCount 11234 15 = 6 ∧ acceleratedOrbit 15 11234 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11234 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11234) = 3 ^ 6 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11234.1, data_15_11234.2]

/-- Complete interval computation for depth 15, residue 11235. -/
theorem bounds_15_11235 : exactInterval 15 11235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11235 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11235) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11235 : oddCount 11235 15 = 6 ∧ acceleratedOrbit 15 11235 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11235 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11235) = 3 ^ 6 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11235.1, data_15_11235.2]

/-- Complete interval computation for depth 15, residue 11236. -/
theorem bounds_15_11236 : exactInterval 15 11236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11236 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11236) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11236 : oddCount 11236 15 = 7 ∧ acceleratedOrbit 15 11236 = 751 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11236 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11236) = 3 ^ 7 * m + 751 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11236.1, data_15_11236.2]

/-- Complete interval computation for depth 15, residue 11237. -/
theorem bounds_15_11237 : exactInterval 15 11237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11237 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11237) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11237 : oddCount 11237 15 = 7 ∧ acceleratedOrbit 15 11237 = 751 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11237 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11237) = 3 ^ 7 * m + 751 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11237.1, data_15_11237.2]

/-- Complete interval computation for depth 15, residue 11238. -/
theorem bounds_15_11238 : exactInterval 15 11238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11238 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11238) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11238 : oddCount 11238 15 = 7 ∧ acceleratedOrbit 15 11238 = 751 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11238 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11238) = 3 ^ 7 * m + 751 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11238.1, data_15_11238.2]

end Collatz.Research.PassageAtlas.Batch0343
