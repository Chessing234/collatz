import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0709

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 23199. -/
theorem bounds_15_23199 : exactInterval 15 23199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23199 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23199) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23199 : oddCount 23199 15 = 9 ∧ acceleratedOrbit 15 23199 = 13936 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23199 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23199) = 3 ^ 9 * m + 13936 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23199.1, data_15_23199.2]

/-- Complete interval computation for depth 15, residue 23200. -/
theorem bounds_15_23200 : exactInterval 15 23200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23200 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23200) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23200 : oddCount 23200 15 = 3 ∧ acceleratedOrbit 15 23200 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23200 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23200) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23200.1, data_15_23200.2]

/-- Complete interval computation for depth 15, residue 23201. -/
theorem bounds_15_23201 : exactInterval 15 23201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23201 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23201) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23201 : oddCount 23201 15 = 10 ∧ acceleratedOrbit 15 23201 = 41816 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23201 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23201) = 3 ^ 10 * m + 41816 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23201.1, data_15_23201.2]

/-- Complete interval computation for depth 15, residue 23202. -/
theorem bounds_15_23202 : exactInterval 15 23202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23202 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23202) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23202 : oddCount 23202 15 = 9 ∧ acceleratedOrbit 15 23202 = 13942 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23202 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23202) = 3 ^ 9 * m + 13942 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23202.1, data_15_23202.2]

/-- Complete interval computation for depth 15, residue 23203. -/
theorem bounds_15_23203 : exactInterval 15 23203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23203 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23203) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23203 : oddCount 23203 15 = 9 ∧ acceleratedOrbit 15 23203 = 13942 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23203 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23203) = 3 ^ 9 * m + 13942 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23203.1, data_15_23203.2]

/-- Complete interval computation for depth 15, residue 23204. -/
theorem bounds_15_23204 : exactInterval 15 23204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23204 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23204) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23204 : oddCount 23204 15 = 9 ∧ acceleratedOrbit 15 23204 = 13942 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23204 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23204) = 3 ^ 9 * m + 13942 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23204.1, data_15_23204.2]

/-- Complete interval computation for depth 15, residue 23205. -/
theorem bounds_15_23205 : exactInterval 15 23205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23205 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23205) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23205 : oddCount 23205 15 = 9 ∧ acceleratedOrbit 15 23205 = 13942 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23205 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23205) = 3 ^ 9 * m + 13942 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23205.1, data_15_23205.2]

/-- Complete interval computation for depth 15, residue 23206. -/
theorem bounds_15_23206 : exactInterval 15 23206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23206 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23206) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23206 : oddCount 23206 15 = 9 ∧ acceleratedOrbit 15 23206 = 13942 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23206 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23206) = 3 ^ 9 * m + 13942 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23206.1, data_15_23206.2]

/-- Complete interval computation for depth 15, residue 23207. -/
theorem bounds_15_23207 : exactInterval 15 23207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23207 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23207) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23207 : oddCount 23207 15 = 12 ∧ acceleratedOrbit 15 23207 = 376406 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23207 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23207) = 3 ^ 12 * m + 376406 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23207.1, data_15_23207.2]

/-- Complete interval computation for depth 15, residue 23208. -/
theorem bounds_15_23208 : exactInterval 15 23208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23208 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23208) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23208 : oddCount 23208 15 = 3 ∧ acceleratedOrbit 15 23208 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23208 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23208) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23208.1, data_15_23208.2]

/-- Complete interval computation for depth 15, residue 23209. -/
theorem bounds_15_23209 : exactInterval 15 23209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23209 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23209) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23209 : oddCount 23209 15 = 11 ∧ acceleratedOrbit 15 23209 = 125479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23209 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23209) = 3 ^ 11 * m + 125479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23209.1, data_15_23209.2]

/-- Complete interval computation for depth 15, residue 23210. -/
theorem bounds_15_23210 : exactInterval 15 23210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23210 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23210) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23210 : oddCount 23210 15 = 3 ∧ acceleratedOrbit 15 23210 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23210 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23210) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23210.1, data_15_23210.2]

/-- Complete interval computation for depth 15, residue 23211. -/
theorem bounds_15_23211 : exactInterval 15 23211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23211 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23211) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23211 : oddCount 23211 15 = 9 ∧ acceleratedOrbit 15 23211 = 13945 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23211 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23211) = 3 ^ 9 * m + 13945 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23211.1, data_15_23211.2]

/-- Complete interval computation for depth 15, residue 23212. -/
theorem bounds_15_23212 : exactInterval 15 23212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23212 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23212) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23212 : oddCount 23212 15 = 7 ∧ acceleratedOrbit 15 23212 = 1550 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23212 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23212) = 3 ^ 7 * m + 1550 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23212.1, data_15_23212.2]

/-- Complete interval computation for depth 15, residue 23213. -/
theorem bounds_15_23213 : exactInterval 15 23213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23213 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23213) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23213 : oddCount 23213 15 = 7 ∧ acceleratedOrbit 15 23213 = 1550 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23213 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23213) = 3 ^ 7 * m + 1550 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23213.1, data_15_23213.2]

/-- Complete interval computation for depth 15, residue 23214. -/
theorem bounds_15_23214 : exactInterval 15 23214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23214 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23214) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23214 : oddCount 23214 15 = 7 ∧ acceleratedOrbit 15 23214 = 1550 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23214 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23214) = 3 ^ 7 * m + 1550 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23214.1, data_15_23214.2]

/-- Complete interval computation for depth 15, residue 23215. -/
theorem bounds_15_23215 : exactInterval 15 23215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23215 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23215) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23215 : oddCount 23215 15 = 7 ∧ acceleratedOrbit 15 23215 = 1550 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23215 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23215) = 3 ^ 7 * m + 1550 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23215.1, data_15_23215.2]

/-- Complete interval computation for depth 15, residue 23216. -/
theorem bounds_15_23216 : exactInterval 15 23216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23216 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23216) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23216 : oddCount 23216 15 = 7 ∧ acceleratedOrbit 15 23216 = 1552 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23216 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23216) = 3 ^ 7 * m + 1552 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23216.1, data_15_23216.2]

/-- Complete interval computation for depth 15, residue 23217. -/
theorem bounds_15_23217 : exactInterval 15 23217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23217 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23217) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23217 : oddCount 23217 15 = 6 ∧ acceleratedOrbit 15 23217 = 517 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23217 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23217) = 3 ^ 6 * m + 517 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23217.1, data_15_23217.2]

/-- Complete interval computation for depth 15, residue 23218. -/
theorem bounds_15_23218 : exactInterval 15 23218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23218 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23218) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23218 : oddCount 23218 15 = 6 ∧ acceleratedOrbit 15 23218 = 517 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23218 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23218) = 3 ^ 6 * m + 517 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23218.1, data_15_23218.2]

/-- Complete interval computation for depth 15, residue 23219. -/
theorem bounds_15_23219 : exactInterval 15 23219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23219 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23219) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23219 : oddCount 23219 15 = 6 ∧ acceleratedOrbit 15 23219 = 517 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23219 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23219) = 3 ^ 6 * m + 517 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23219.1, data_15_23219.2]

/-- Complete interval computation for depth 15, residue 23220. -/
theorem bounds_15_23220 : exactInterval 15 23220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23220 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23220) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23220 : oddCount 23220 15 = 7 ∧ acceleratedOrbit 15 23220 = 1552 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23220 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23220) = 3 ^ 7 * m + 1552 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23220.1, data_15_23220.2]

/-- Complete interval computation for depth 15, residue 23221. -/
theorem bounds_15_23221 : exactInterval 15 23221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23221 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23221) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23221 : oddCount 23221 15 = 7 ∧ acceleratedOrbit 15 23221 = 1552 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23221 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23221) = 3 ^ 7 * m + 1552 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23221.1, data_15_23221.2]

/-- Complete interval computation for depth 15, residue 23222. -/
theorem bounds_15_23222 : exactInterval 15 23222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23222 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23222) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23222 : oddCount 23222 15 = 9 ∧ acceleratedOrbit 15 23222 = 13952 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23222 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23222) = 3 ^ 9 * m + 13952 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23222.1, data_15_23222.2]

/-- Complete interval computation for depth 15, residue 23223. -/
theorem bounds_15_23223 : exactInterval 15 23223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23223 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23223) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23223 : oddCount 23223 15 = 9 ∧ acceleratedOrbit 15 23223 = 13952 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23223 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23223) = 3 ^ 9 * m + 13952 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23223.1, data_15_23223.2]

/-- Complete interval computation for depth 15, residue 23224. -/
theorem bounds_15_23224 : exactInterval 15 23224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23224 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23224) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23224 : oddCount 23224 15 = 7 ∧ acceleratedOrbit 15 23224 = 1552 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23224 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23224) = 3 ^ 7 * m + 1552 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23224.1, data_15_23224.2]

/-- Complete interval computation for depth 15, residue 23225. -/
theorem bounds_15_23225 : exactInterval 15 23225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23225 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23225) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23225 : oddCount 23225 15 = 6 ∧ acceleratedOrbit 15 23225 = 517 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23225 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23225) = 3 ^ 6 * m + 517 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23225.1, data_15_23225.2]

/-- Complete interval computation for depth 15, residue 23226. -/
theorem bounds_15_23226 : exactInterval 15 23226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23226 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23226) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23226 : oddCount 23226 15 = 7 ∧ acceleratedOrbit 15 23226 = 1552 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23226 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23226) = 3 ^ 7 * m + 1552 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23226.1, data_15_23226.2]

/-- Complete interval computation for depth 15, residue 23227. -/
theorem bounds_15_23227 : exactInterval 15 23227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23227 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23227) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23227 : oddCount 23227 15 = 9 ∧ acceleratedOrbit 15 23227 = 13954 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23227 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23227) = 3 ^ 9 * m + 13954 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23227.1, data_15_23227.2]

/-- Complete interval computation for depth 15, residue 23228. -/
theorem bounds_15_23228 : exactInterval 15 23228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23228 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23228) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23228 : oddCount 23228 15 = 9 ∧ acceleratedOrbit 15 23228 = 13958 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23228 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23228) = 3 ^ 9 * m + 13958 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23228.1, data_15_23228.2]

/-- Complete interval computation for depth 15, residue 23229. -/
theorem bounds_15_23229 : exactInterval 15 23229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23229 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23229) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23229 : oddCount 23229 15 = 9 ∧ acceleratedOrbit 15 23229 = 13958 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23229 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23229) = 3 ^ 9 * m + 13958 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23229.1, data_15_23229.2]

/-- Complete interval computation for depth 15, residue 23230. -/
theorem bounds_15_23230 : exactInterval 15 23230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23230 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23230) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23230 : oddCount 23230 15 = 9 ∧ acceleratedOrbit 15 23230 = 13958 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23230 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23230) = 3 ^ 9 * m + 13958 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23230.1, data_15_23230.2]

/-- Complete interval computation for depth 15, residue 23231. -/
theorem bounds_15_23231 : exactInterval 15 23231 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23231 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23231) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23231 : oddCount 23231 15 = 9 ∧ acceleratedOrbit 15 23231 = 13955 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23231 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23231) = 3 ^ 9 * m + 13955 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23231.1, data_15_23231.2]

end Collatz.Research.PassageAtlas.Batch0709
