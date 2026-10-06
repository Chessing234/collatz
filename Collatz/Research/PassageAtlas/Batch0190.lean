import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0190

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 6193. -/
theorem bounds_15_6193 : exactInterval 15 6193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6193 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6193) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6193 : oddCount 6193 15 = 10 ∧ acceleratedOrbit 15 6193 = 11177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6193 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6193) = 3 ^ 10 * m + 11177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6193.1, data_15_6193.2]

/-- Complete interval computation for depth 15, residue 6194. -/
theorem bounds_15_6194 : exactInterval 15 6194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6194 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6194) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6194 : oddCount 6194 15 = 10 ∧ acceleratedOrbit 15 6194 = 11177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6194 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6194) = 3 ^ 10 * m + 11177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6194.1, data_15_6194.2]

/-- Complete interval computation for depth 15, residue 6195. -/
theorem bounds_15_6195 : exactInterval 15 6195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6195 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6195) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6195 : oddCount 6195 15 = 10 ∧ acceleratedOrbit 15 6195 = 11177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6195 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6195) = 3 ^ 10 * m + 11177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6195.1, data_15_6195.2]

/-- Complete interval computation for depth 15, residue 6196. -/
theorem bounds_15_6196 : exactInterval 15 6196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6196 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6196) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6196 : oddCount 6196 15 = 5 ∧ acceleratedOrbit 15 6196 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6196 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6196) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6196.1, data_15_6196.2]

/-- Complete interval computation for depth 15, residue 6197. -/
theorem bounds_15_6197 : exactInterval 15 6197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6197 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6197) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6197 : oddCount 6197 15 = 5 ∧ acceleratedOrbit 15 6197 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6197 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6197) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6197.1, data_15_6197.2]

/-- Complete interval computation for depth 15, residue 6198. -/
theorem bounds_15_6198 : exactInterval 15 6198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6198 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6198) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6198 : oddCount 6198 15 = 11 ∧ acceleratedOrbit 15 6198 = 33524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6198 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6198) = 3 ^ 11 * m + 33524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6198.1, data_15_6198.2]

/-- Complete interval computation for depth 15, residue 6199. -/
theorem bounds_15_6199 : exactInterval 15 6199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6199 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6199) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6199 : oddCount 6199 15 = 11 ∧ acceleratedOrbit 15 6199 = 33524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6199 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6199) = 3 ^ 11 * m + 33524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6199.1, data_15_6199.2]

/-- Complete interval computation for depth 15, residue 6200. -/
theorem bounds_15_6200 : exactInterval 15 6200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6200 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6200) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6200 : oddCount 6200 15 = 7 ∧ acceleratedOrbit 15 6200 = 415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6200 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6200) = 3 ^ 7 * m + 415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6200.1, data_15_6200.2]

/-- Complete interval computation for depth 15, residue 6201. -/
theorem bounds_15_6201 : exactInterval 15 6201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6201 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6201) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6201 : oddCount 6201 15 = 5 ∧ acceleratedOrbit 15 6201 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6201 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6201) = 3 ^ 5 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6201.1, data_15_6201.2]

/-- Complete interval computation for depth 15, residue 6202. -/
theorem bounds_15_6202 : exactInterval 15 6202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6202 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6202) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6202 : oddCount 6202 15 = 7 ∧ acceleratedOrbit 15 6202 = 415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6202 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6202) = 3 ^ 7 * m + 415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6202.1, data_15_6202.2]

/-- Complete interval computation for depth 15, residue 6203. -/
theorem bounds_15_6203 : exactInterval 15 6203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6203 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6203) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6203 : oddCount 6203 15 = 8 ∧ acceleratedOrbit 15 6203 = 1243 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6203 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6203) = 3 ^ 8 * m + 1243 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6203.1, data_15_6203.2]

/-- Complete interval computation for depth 15, residue 6204. -/
theorem bounds_15_6204 : exactInterval 15 6204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6204 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6204) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6204 : oddCount 6204 15 = 7 ∧ acceleratedOrbit 15 6204 = 415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6204 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6204) = 3 ^ 7 * m + 415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6204.1, data_15_6204.2]

/-- Complete interval computation for depth 15, residue 6205. -/
theorem bounds_15_6205 : exactInterval 15 6205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6205 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6205) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6205 : oddCount 6205 15 = 7 ∧ acceleratedOrbit 15 6205 = 415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6205 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6205) = 3 ^ 7 * m + 415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6205.1, data_15_6205.2]

/-- Complete interval computation for depth 15, residue 6206. -/
theorem bounds_15_6206 : exactInterval 15 6206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6206 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6206) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6206 : oddCount 6206 15 = 10 ∧ acceleratedOrbit 15 6206 = 11188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6206 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6206) = 3 ^ 10 * m + 11188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6206.1, data_15_6206.2]

/-- Complete interval computation for depth 15, residue 6207. -/
theorem bounds_15_6207 : exactInterval 15 6207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6207 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6207) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6207 : oddCount 6207 15 = 10 ∧ acceleratedOrbit 15 6207 = 11188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6207 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6207) = 3 ^ 10 * m + 11188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6207.1, data_15_6207.2]

/-- Complete interval computation for depth 15, residue 6208. -/
theorem bounds_15_6208 : exactInterval 15 6208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6208 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6208) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6208 : oddCount 6208 15 = 5 ∧ acceleratedOrbit 15 6208 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6208 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6208) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6208.1, data_15_6208.2]

/-- Complete interval computation for depth 15, residue 6209. -/
theorem bounds_15_6209 : exactInterval 15 6209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6209 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6209) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6209 : oddCount 6209 15 = 7 ∧ acceleratedOrbit 15 6209 = 415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6209 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6209) = 3 ^ 7 * m + 415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6209.1, data_15_6209.2]

/-- Complete interval computation for depth 15, residue 6210. -/
theorem bounds_15_6210 : exactInterval 15 6210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6210 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6210) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6210 : oddCount 6210 15 = 7 ∧ acceleratedOrbit 15 6210 = 415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6210 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6210) = 3 ^ 7 * m + 415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6210.1, data_15_6210.2]

/-- Complete interval computation for depth 15, residue 6211. -/
theorem bounds_15_6211 : exactInterval 15 6211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6211 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6211) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6211 : oddCount 6211 15 = 7 ∧ acceleratedOrbit 15 6211 = 415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6211 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6211) = 3 ^ 7 * m + 415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6211.1, data_15_6211.2]

/-- Complete interval computation for depth 15, residue 6212. -/
theorem bounds_15_6212 : exactInterval 15 6212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6212 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6212) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6212 : oddCount 6212 15 = 5 ∧ acceleratedOrbit 15 6212 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6212 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6212) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6212.1, data_15_6212.2]

/-- Complete interval computation for depth 15, residue 6213. -/
theorem bounds_15_6213 : exactInterval 15 6213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6213 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6213) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6213 : oddCount 6213 15 = 5 ∧ acceleratedOrbit 15 6213 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6213 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6213) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6213.1, data_15_6213.2]

/-- Complete interval computation for depth 15, residue 6214. -/
theorem bounds_15_6214 : exactInterval 15 6214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6214 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6214) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6214 : oddCount 6214 15 = 5 ∧ acceleratedOrbit 15 6214 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6214 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6214) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6214.1, data_15_6214.2]

/-- Complete interval computation for depth 15, residue 6215. -/
theorem bounds_15_6215 : exactInterval 15 6215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6215 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6215) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6215 : oddCount 6215 15 = 10 ∧ acceleratedOrbit 15 6215 = 11204 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6215 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6215) = 3 ^ 10 * m + 11204 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6215.1, data_15_6215.2]

/-- Complete interval computation for depth 15, residue 6216. -/
theorem bounds_15_6216 : exactInterval 15 6216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6216 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6216) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6216 : oddCount 6216 15 = 7 ∧ acceleratedOrbit 15 6216 = 416 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6216 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6216) = 3 ^ 7 * m + 416 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6216.1, data_15_6216.2]

/-- Complete interval computation for depth 15, residue 6217. -/
theorem bounds_15_6217 : exactInterval 15 6217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6217 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6217) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6217 : oddCount 6217 15 = 9 ∧ acceleratedOrbit 15 6217 = 3736 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6217 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6217) = 3 ^ 9 * m + 3736 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6217.1, data_15_6217.2]

/-- Complete interval computation for depth 15, residue 6218. -/
theorem bounds_15_6218 : exactInterval 15 6218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6218 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6218) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6218 : oddCount 6218 15 = 7 ∧ acceleratedOrbit 15 6218 = 416 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6218 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6218) = 3 ^ 7 * m + 416 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6218.1, data_15_6218.2]

/-- Complete interval computation for depth 15, residue 6219. -/
theorem bounds_15_6219 : exactInterval 15 6219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6219 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6219) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6219 : oddCount 6219 15 = 5 ∧ acceleratedOrbit 15 6219 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6219 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6219) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6219.1, data_15_6219.2]

/-- Complete interval computation for depth 15, residue 6220. -/
theorem bounds_15_6220 : exactInterval 15 6220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6220 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6220) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6220 : oddCount 6220 15 = 7 ∧ acceleratedOrbit 15 6220 = 416 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6220 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6220) = 3 ^ 7 * m + 416 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6220.1, data_15_6220.2]

/-- Complete interval computation for depth 15, residue 6221. -/
theorem bounds_15_6221 : exactInterval 15 6221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6221 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6221) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6221 : oddCount 6221 15 = 7 ∧ acceleratedOrbit 15 6221 = 416 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6221 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6221) = 3 ^ 7 * m + 416 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6221.1, data_15_6221.2]

/-- Complete interval computation for depth 15, residue 6222. -/
theorem bounds_15_6222 : exactInterval 15 6222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6222 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6222) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6222 : oddCount 6222 15 = 7 ∧ acceleratedOrbit 15 6222 = 416 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6222 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6222) = 3 ^ 7 * m + 416 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6222.1, data_15_6222.2]

/-- Complete interval computation for depth 15, residue 6223. -/
theorem bounds_15_6223 : exactInterval 15 6223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6223 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6223) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6223 : oddCount 6223 15 = 7 ∧ acceleratedOrbit 15 6223 = 416 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6223 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6223) = 3 ^ 7 * m + 416 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6223.1, data_15_6223.2]

/-- Complete interval computation for depth 15, residue 6224. -/
theorem bounds_15_6224 : exactInterval 15 6224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6224 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6224) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6224 : oddCount 6224 15 = 5 ∧ acceleratedOrbit 15 6224 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6224 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6224) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6224.1, data_15_6224.2]

end Collatz.Research.PassageAtlas.Batch0190
