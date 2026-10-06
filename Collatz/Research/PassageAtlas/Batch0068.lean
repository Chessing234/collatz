import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0068

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 2195. -/
theorem bounds_15_2195 : exactInterval 15 2195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2195 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2195) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2195 : oddCount 2195 15 = 9 ∧ acceleratedOrbit 15 2195 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2195 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2195) = 3 ^ 9 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2195.1, data_15_2195.2]

/-- Complete interval computation for depth 15, residue 2196. -/
theorem bounds_15_2196 : exactInterval 15 2196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2196 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2196) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2196 : oddCount 2196 15 = 8 ∧ acceleratedOrbit 15 2196 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2196 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2196) = 3 ^ 8 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2196.1, data_15_2196.2]

/-- Complete interval computation for depth 15, residue 2197. -/
theorem bounds_15_2197 : exactInterval 15 2197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2197 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2197) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2197 : oddCount 2197 15 = 8 ∧ acceleratedOrbit 15 2197 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2197 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2197) = 3 ^ 8 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2197.1, data_15_2197.2]

/-- Complete interval computation for depth 15, residue 2198. -/
theorem bounds_15_2198 : exactInterval 15 2198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2198 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2198) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2198 : oddCount 2198 15 = 5 ∧ acceleratedOrbit 15 2198 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2198 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2198) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2198.1, data_15_2198.2]

/-- Complete interval computation for depth 15, residue 2199. -/
theorem bounds_15_2199 : exactInterval 15 2199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2199 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2199) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2199 : oddCount 2199 15 = 5 ∧ acceleratedOrbit 15 2199 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2199 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2199) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2199.1, data_15_2199.2]

/-- Complete interval computation for depth 15, residue 2200. -/
theorem bounds_15_2200 : exactInterval 15 2200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2200 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2200) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2200 : oddCount 2200 15 = 8 ∧ acceleratedOrbit 15 2200 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2200 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2200) = 3 ^ 8 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2200.1, data_15_2200.2]

/-- Complete interval computation for depth 15, residue 2201. -/
theorem bounds_15_2201 : exactInterval 15 2201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2201 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2201) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2201 : oddCount 2201 15 = 8 ∧ acceleratedOrbit 15 2201 = 442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2201 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2201) = 3 ^ 8 * m + 442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2201.1, data_15_2201.2]

/-- Complete interval computation for depth 15, residue 2202. -/
theorem bounds_15_2202 : exactInterval 15 2202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2202 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2202) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2202 : oddCount 2202 15 = 8 ∧ acceleratedOrbit 15 2202 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2202 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2202) = 3 ^ 8 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2202.1, data_15_2202.2]

/-- Complete interval computation for depth 15, residue 2203. -/
theorem bounds_15_2203 : exactInterval 15 2203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2203 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2203) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2203 : oddCount 2203 15 = 9 ∧ acceleratedOrbit 15 2203 = 1325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2203 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2203) = 3 ^ 9 * m + 1325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2203.1, data_15_2203.2]

/-- Complete interval computation for depth 15, residue 2204. -/
theorem bounds_15_2204 : exactInterval 15 2204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2204 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2204) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2204 : oddCount 2204 15 = 7 ∧ acceleratedOrbit 15 2204 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2204 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2204) = 3 ^ 7 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2204.1, data_15_2204.2]

/-- Complete interval computation for depth 15, residue 2205. -/
theorem bounds_15_2205 : exactInterval 15 2205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2205 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2205) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2205 : oddCount 2205 15 = 7 ∧ acceleratedOrbit 15 2205 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2205 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2205) = 3 ^ 7 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2205.1, data_15_2205.2]

/-- Complete interval computation for depth 15, residue 2206. -/
theorem bounds_15_2206 : exactInterval 15 2206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2206 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2206) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2206 : oddCount 2206 15 = 7 ∧ acceleratedOrbit 15 2206 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2206 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2206) = 3 ^ 7 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2206.1, data_15_2206.2]

/-- Complete interval computation for depth 15, residue 2207. -/
theorem bounds_15_2207 : exactInterval 15 2207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2207 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2207) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2207 : oddCount 2207 15 = 12 ∧ acceleratedOrbit 15 2207 = 35812 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2207 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2207) = 3 ^ 12 * m + 35812 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2207.1, data_15_2207.2]

/-- Complete interval computation for depth 15, residue 2208. -/
theorem bounds_15_2208 : exactInterval 15 2208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2208 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2208) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2208 : oddCount 2208 15 = 3 ∧ acceleratedOrbit 15 2208 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2208 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2208) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2208.1, data_15_2208.2]

/-- Complete interval computation for depth 15, residue 2209. -/
theorem bounds_15_2209 : exactInterval 15 2209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2209 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2209) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2209 : oddCount 2209 15 = 8 ∧ acceleratedOrbit 15 2209 = 443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2209 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2209) = 3 ^ 8 * m + 443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2209.1, data_15_2209.2]

/-- Complete interval computation for depth 15, residue 2210. -/
theorem bounds_15_2210 : exactInterval 15 2210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2210 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2210) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2210 : oddCount 2210 15 = 8 ∧ acceleratedOrbit 15 2210 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2210 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2210) = 3 ^ 8 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2210.1, data_15_2210.2]

/-- Complete interval computation for depth 15, residue 2211. -/
theorem bounds_15_2211 : exactInterval 15 2211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2211 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2211) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2211 : oddCount 2211 15 = 8 ∧ acceleratedOrbit 15 2211 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2211 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2211) = 3 ^ 8 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2211.1, data_15_2211.2]

/-- Complete interval computation for depth 15, residue 2212. -/
theorem bounds_15_2212 : exactInterval 15 2212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2212 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2212) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2212 : oddCount 2212 15 = 9 ∧ acceleratedOrbit 15 2212 = 1333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2212 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2212) = 3 ^ 9 * m + 1333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2212.1, data_15_2212.2]

/-- Complete interval computation for depth 15, residue 2213. -/
theorem bounds_15_2213 : exactInterval 15 2213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2213 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2213) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2213 : oddCount 2213 15 = 9 ∧ acceleratedOrbit 15 2213 = 1333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2213 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2213) = 3 ^ 9 * m + 1333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2213.1, data_15_2213.2]

/-- Complete interval computation for depth 15, residue 2214. -/
theorem bounds_15_2214 : exactInterval 15 2214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2214 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2214) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2214 : oddCount 2214 15 = 9 ∧ acceleratedOrbit 15 2214 = 1333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2214 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2214) = 3 ^ 9 * m + 1333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2214.1, data_15_2214.2]

/-- Complete interval computation for depth 15, residue 2215. -/
theorem bounds_15_2215 : exactInterval 15 2215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2215 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2215) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2215 : oddCount 2215 15 = 11 ∧ acceleratedOrbit 15 2215 = 11983 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2215 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2215) = 3 ^ 11 * m + 11983 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2215.1, data_15_2215.2]

/-- Complete interval computation for depth 15, residue 2216. -/
theorem bounds_15_2216 : exactInterval 15 2216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2216 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2216) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2216 : oddCount 2216 15 = 3 ∧ acceleratedOrbit 15 2216 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2216 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2216) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2216.1, data_15_2216.2]

/-- Complete interval computation for depth 15, residue 2217. -/
theorem bounds_15_2217 : exactInterval 15 2217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2217 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2217) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2217 : oddCount 2217 15 = 12 ∧ acceleratedOrbit 15 2217 = 35984 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2217 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2217) = 3 ^ 12 * m + 35984 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2217.1, data_15_2217.2]

/-- Complete interval computation for depth 15, residue 2218. -/
theorem bounds_15_2218 : exactInterval 15 2218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2218 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2218) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2218 : oddCount 2218 15 = 3 ∧ acceleratedOrbit 15 2218 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2218 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2218) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2218.1, data_15_2218.2]

/-- Complete interval computation for depth 15, residue 2219. -/
theorem bounds_15_2219 : exactInterval 15 2219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2219 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2219) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2219 : oddCount 2219 15 = 9 ∧ acceleratedOrbit 15 2219 = 1336 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2219 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2219) = 3 ^ 9 * m + 1336 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2219.1, data_15_2219.2]

/-- Complete interval computation for depth 15, residue 2220. -/
theorem bounds_15_2220 : exactInterval 15 2220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2220 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2220) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2220 : oddCount 2220 15 = 5 ∧ acceleratedOrbit 15 2220 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2220 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2220) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2220.1, data_15_2220.2]

/-- Complete interval computation for depth 15, residue 2221. -/
theorem bounds_15_2221 : exactInterval 15 2221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2221 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2221) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2221 : oddCount 2221 15 = 5 ∧ acceleratedOrbit 15 2221 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2221 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2221) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2221.1, data_15_2221.2]

/-- Complete interval computation for depth 15, residue 2222. -/
theorem bounds_15_2222 : exactInterval 15 2222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2222 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2222) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2222 : oddCount 2222 15 = 5 ∧ acceleratedOrbit 15 2222 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2222 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2222) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2222.1, data_15_2222.2]

/-- Complete interval computation for depth 15, residue 2223. -/
theorem bounds_15_2223 : exactInterval 15 2223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2223 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2223) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2223 : oddCount 2223 15 = 11 ∧ acceleratedOrbit 15 2223 = 12028 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2223 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2223) = 3 ^ 11 * m + 12028 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2223.1, data_15_2223.2]

/-- Complete interval computation for depth 15, residue 2224. -/
theorem bounds_15_2224 : exactInterval 15 2224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2224 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2224) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2224 : oddCount 2224 15 = 7 ∧ acceleratedOrbit 15 2224 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2224 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2224) = 3 ^ 7 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2224.1, data_15_2224.2]

/-- Complete interval computation for depth 15, residue 2225. -/
theorem bounds_15_2225 : exactInterval 15 2225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2225 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2225) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2225 : oddCount 2225 15 = 8 ∧ acceleratedOrbit 15 2225 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2225 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2225) = 3 ^ 8 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2225.1, data_15_2225.2]

/-- Complete interval computation for depth 15, residue 2226. -/
theorem bounds_15_2226 : exactInterval 15 2226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2226 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2226) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2226 : oddCount 2226 15 = 8 ∧ acceleratedOrbit 15 2226 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2226 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2226) = 3 ^ 8 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2226.1, data_15_2226.2]

/-- Complete interval computation for depth 15, residue 2227. -/
theorem bounds_15_2227 : exactInterval 15 2227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2227 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2227) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2227 : oddCount 2227 15 = 8 ∧ acceleratedOrbit 15 2227 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2227 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2227) = 3 ^ 8 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2227.1, data_15_2227.2]

end Collatz.Research.PassageAtlas.Batch0068
