import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0282

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 9207. -/
theorem bounds_15_9207 : exactInterval 15 9207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9207 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9207) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9207 : oddCount 9207 15 = 9 ∧ acceleratedOrbit 15 9207 = 5534 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9207 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9207) = 3 ^ 9 * m + 5534 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9207.1, data_15_9207.2]

/-- Complete interval computation for depth 15, residue 9208. -/
theorem bounds_15_9208 : exactInterval 15 9208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9208 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9208) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9208 : oddCount 9208 15 = 9 ∧ acceleratedOrbit 15 9208 = 5536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9208 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9208) = 3 ^ 9 * m + 5536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9208.1, data_15_9208.2]

/-- Complete interval computation for depth 15, residue 9209. -/
theorem bounds_15_9209 : exactInterval 15 9209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9209 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9209) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9209 : oddCount 9209 15 = 10 ∧ acceleratedOrbit 15 9209 = 16600 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9209 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9209) = 3 ^ 10 * m + 16600 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9209.1, data_15_9209.2]

/-- Complete interval computation for depth 15, residue 9210. -/
theorem bounds_15_9210 : exactInterval 15 9210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9210 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9210) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9210 : oddCount 9210 15 = 9 ∧ acceleratedOrbit 15 9210 = 5536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9210 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9210) = 3 ^ 9 * m + 5536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9210.1, data_15_9210.2]

/-- Complete interval computation for depth 15, residue 9211. -/
theorem bounds_15_9211 : exactInterval 15 9211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9211 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9211) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9211 : oddCount 9211 15 = 10 ∧ acceleratedOrbit 15 9211 = 16604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9211 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9211) = 3 ^ 10 * m + 16604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9211.1, data_15_9211.2]

/-- Complete interval computation for depth 15, residue 9212. -/
theorem bounds_15_9212 : exactInterval 15 9212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9212 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9212) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9212 : oddCount 9212 15 = 9 ∧ acceleratedOrbit 15 9212 = 5536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9212 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9212) = 3 ^ 9 * m + 5536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9212.1, data_15_9212.2]

/-- Complete interval computation for depth 15, residue 9213. -/
theorem bounds_15_9213 : exactInterval 15 9213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9213 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9213) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9213 : oddCount 9213 15 = 9 ∧ acceleratedOrbit 15 9213 = 5536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9213 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9213) = 3 ^ 9 * m + 5536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9213.1, data_15_9213.2]

/-- Complete interval computation for depth 15, residue 9214. -/
theorem bounds_15_9214 : exactInterval 15 9214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9214 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9214) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9214 : oddCount 9214 15 = 11 ∧ acceleratedOrbit 15 9214 = 49823 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9214 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9214) = 3 ^ 11 * m + 49823 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9214.1, data_15_9214.2]

/-- Complete interval computation for depth 15, residue 9215. -/
theorem bounds_15_9215 : exactInterval 15 9215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9215 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9215) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9215 : oddCount 9215 15 = 11 ∧ acceleratedOrbit 15 9215 = 49823 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9215 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9215) = 3 ^ 11 * m + 49823 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9215.1, data_15_9215.2]

/-- Complete interval computation for depth 15, residue 9216. -/
theorem bounds_15_9216 : exactInterval 15 9216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9216 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9216) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9216 : oddCount 9216 15 = 4 ∧ acceleratedOrbit 15 9216 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9216 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9216) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9216.1, data_15_9216.2]

/-- Complete interval computation for depth 15, residue 9217. -/
theorem bounds_15_9217 : exactInterval 15 9217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9217 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9217) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9217 : oddCount 9217 15 = 7 ∧ acceleratedOrbit 15 9217 = 616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9217 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9217) = 3 ^ 7 * m + 616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9217.1, data_15_9217.2]

/-- Complete interval computation for depth 15, residue 9218. -/
theorem bounds_15_9218 : exactInterval 15 9218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9218 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9218) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9218 : oddCount 9218 15 = 7 ∧ acceleratedOrbit 15 9218 = 616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9218 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9218) = 3 ^ 7 * m + 616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9218.1, data_15_9218.2]

/-- Complete interval computation for depth 15, residue 9219. -/
theorem bounds_15_9219 : exactInterval 15 9219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9219 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9219) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9219 : oddCount 9219 15 = 7 ∧ acceleratedOrbit 15 9219 = 616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9219 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9219) = 3 ^ 7 * m + 616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9219.1, data_15_9219.2]

/-- Complete interval computation for depth 15, residue 9220. -/
theorem bounds_15_9220 : exactInterval 15 9220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9220 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9220) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9220 : oddCount 9220 15 = 6 ∧ acceleratedOrbit 15 9220 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9220 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9220) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9220.1, data_15_9220.2]

/-- Complete interval computation for depth 15, residue 9221. -/
theorem bounds_15_9221 : exactInterval 15 9221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9221 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9221) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9221 : oddCount 9221 15 = 6 ∧ acceleratedOrbit 15 9221 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9221 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9221) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9221.1, data_15_9221.2]

/-- Complete interval computation for depth 15, residue 9222. -/
theorem bounds_15_9222 : exactInterval 15 9222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9222 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9222) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9222 : oddCount 9222 15 = 6 ∧ acceleratedOrbit 15 9222 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9222 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9222) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9222.1, data_15_9222.2]

/-- Complete interval computation for depth 15, residue 9223. -/
theorem bounds_15_9223 : exactInterval 15 9223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9223 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9223) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9223 : oddCount 9223 15 = 7 ∧ acceleratedOrbit 15 9223 = 616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9223 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9223) = 3 ^ 7 * m + 616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9223.1, data_15_9223.2]

/-- Complete interval computation for depth 15, residue 9224. -/
theorem bounds_15_9224 : exactInterval 15 9224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9224 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9224) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9224 : oddCount 9224 15 = 8 ∧ acceleratedOrbit 15 9224 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9224 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9224) = 3 ^ 8 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9224.1, data_15_9224.2]

/-- Complete interval computation for depth 15, residue 9225. -/
theorem bounds_15_9225 : exactInterval 15 9225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9225 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9225) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9225 : oddCount 9225 15 = 10 ∧ acceleratedOrbit 15 9225 = 16631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9225 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9225) = 3 ^ 10 * m + 16631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9225.1, data_15_9225.2]

/-- Complete interval computation for depth 15, residue 9226. -/
theorem bounds_15_9226 : exactInterval 15 9226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9226 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9226) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9226 : oddCount 9226 15 = 8 ∧ acceleratedOrbit 15 9226 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9226 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9226) = 3 ^ 8 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9226.1, data_15_9226.2]

/-- Complete interval computation for depth 15, residue 9227. -/
theorem bounds_15_9227 : exactInterval 15 9227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9227 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9227) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9227 : oddCount 9227 15 = 6 ∧ acceleratedOrbit 15 9227 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9227 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9227) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9227.1, data_15_9227.2]

/-- Complete interval computation for depth 15, residue 9228. -/
theorem bounds_15_9228 : exactInterval 15 9228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9228 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9228) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9228 : oddCount 9228 15 = 8 ∧ acceleratedOrbit 15 9228 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9228 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9228) = 3 ^ 8 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9228.1, data_15_9228.2]

/-- Complete interval computation for depth 15, residue 9229. -/
theorem bounds_15_9229 : exactInterval 15 9229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9229 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9229) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9229 : oddCount 9229 15 = 8 ∧ acceleratedOrbit 15 9229 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9229 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9229) = 3 ^ 8 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9229.1, data_15_9229.2]

/-- Complete interval computation for depth 15, residue 9230. -/
theorem bounds_15_9230 : exactInterval 15 9230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9230 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9230) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9230 : oddCount 9230 15 = 9 ∧ acceleratedOrbit 15 9230 = 5548 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9230 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9230) = 3 ^ 9 * m + 5548 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9230.1, data_15_9230.2]

/-- Complete interval computation for depth 15, residue 9231. -/
theorem bounds_15_9231 : exactInterval 15 9231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9231 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9231) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9231 : oddCount 9231 15 = 9 ∧ acceleratedOrbit 15 9231 = 5548 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9231 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9231) = 3 ^ 9 * m + 5548 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9231.1, data_15_9231.2]

/-- Complete interval computation for depth 15, residue 9232. -/
theorem bounds_15_9232 : exactInterval 15 9232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9232 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9232) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9232 : oddCount 9232 15 = 4 ∧ acceleratedOrbit 15 9232 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9232 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9232) = 3 ^ 4 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9232.1, data_15_9232.2]

/-- Complete interval computation for depth 15, residue 9233. -/
theorem bounds_15_9233 : exactInterval 15 9233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9233 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9233) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9233 : oddCount 9233 15 = 8 ∧ acceleratedOrbit 15 9233 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9233 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9233) = 3 ^ 8 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9233.1, data_15_9233.2]

/-- Complete interval computation for depth 15, residue 9234. -/
theorem bounds_15_9234 : exactInterval 15 9234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9234 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9234) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9234 : oddCount 9234 15 = 6 ∧ acceleratedOrbit 15 9234 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9234 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9234) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9234.1, data_15_9234.2]

/-- Complete interval computation for depth 15, residue 9235. -/
theorem bounds_15_9235 : exactInterval 15 9235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9235 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9235) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9235 : oddCount 9235 15 = 6 ∧ acceleratedOrbit 15 9235 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9235 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9235) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9235.1, data_15_9235.2]

/-- Complete interval computation for depth 15, residue 9236. -/
theorem bounds_15_9236 : exactInterval 15 9236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9236 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9236) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9236 : oddCount 9236 15 = 4 ∧ acceleratedOrbit 15 9236 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9236 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9236) = 3 ^ 4 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9236.1, data_15_9236.2]

/-- Complete interval computation for depth 15, residue 9237. -/
theorem bounds_15_9237 : exactInterval 15 9237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9237 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9237) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9237 : oddCount 9237 15 = 4 ∧ acceleratedOrbit 15 9237 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9237 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9237) = 3 ^ 4 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9237.1, data_15_9237.2]

/-- Complete interval computation for depth 15, residue 9238. -/
theorem bounds_15_9238 : exactInterval 15 9238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9238 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9238) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9238 : oddCount 9238 15 = 8 ∧ acceleratedOrbit 15 9238 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9238 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9238) = 3 ^ 8 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9238.1, data_15_9238.2]

/-- Complete interval computation for depth 15, residue 9239. -/
theorem bounds_15_9239 : exactInterval 15 9239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9239 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9239) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9239 : oddCount 9239 15 = 8 ∧ acceleratedOrbit 15 9239 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9239 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9239) = 3 ^ 8 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9239.1, data_15_9239.2]

end Collatz.Research.PassageAtlas.Batch0282
