import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0770

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 25198. -/
theorem bounds_15_25198 : exactInterval 15 25198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25198 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25198) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25198 : oddCount 25198 15 = 7 ∧ acceleratedOrbit 15 25198 = 1682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25198 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25198) = 3 ^ 7 * m + 1682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25198.1, data_15_25198.2]

/-- Complete interval computation for depth 15, residue 25199. -/
theorem bounds_15_25199 : exactInterval 15 25199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25199 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25199) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25199 : oddCount 25199 15 = 10 ∧ acceleratedOrbit 15 25199 = 45413 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25199 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25199) = 3 ^ 10 * m + 45413 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25199.1, data_15_25199.2]

/-- Complete interval computation for depth 15, residue 25200. -/
theorem bounds_15_25200 : exactInterval 15 25200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25200 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25200) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25200 : oddCount 25200 15 = 5 ∧ acceleratedOrbit 15 25200 = 187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25200 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25200) = 3 ^ 5 * m + 187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25200.1, data_15_25200.2]

/-- Complete interval computation for depth 15, residue 25201. -/
theorem bounds_15_25201 : exactInterval 15 25201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25201 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25201) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25201 : oddCount 25201 15 = 6 ∧ acceleratedOrbit 15 25201 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25201 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25201) = 3 ^ 6 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25201.1, data_15_25201.2]

/-- Complete interval computation for depth 15, residue 25202. -/
theorem bounds_15_25202 : exactInterval 15 25202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25202 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25202) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25202 : oddCount 25202 15 = 9 ∧ acceleratedOrbit 15 25202 = 15142 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25202 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25202) = 3 ^ 9 * m + 15142 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25202.1, data_15_25202.2]

/-- Complete interval computation for depth 15, residue 25203. -/
theorem bounds_15_25203 : exactInterval 15 25203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25203 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25203) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25203 : oddCount 25203 15 = 9 ∧ acceleratedOrbit 15 25203 = 15142 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25203 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25203) = 3 ^ 9 * m + 15142 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25203.1, data_15_25203.2]

/-- Complete interval computation for depth 15, residue 25204. -/
theorem bounds_15_25204 : exactInterval 15 25204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25204 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25204) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25204 : oddCount 25204 15 = 5 ∧ acceleratedOrbit 15 25204 = 187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25204 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25204) = 3 ^ 5 * m + 187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25204.1, data_15_25204.2]

/-- Complete interval computation for depth 15, residue 25205. -/
theorem bounds_15_25205 : exactInterval 15 25205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25205 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25205) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25205 : oddCount 25205 15 = 5 ∧ acceleratedOrbit 15 25205 = 187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25205 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25205) = 3 ^ 5 * m + 187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25205.1, data_15_25205.2]

/-- Complete interval computation for depth 15, residue 25206. -/
theorem bounds_15_25206 : exactInterval 15 25206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25206 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25206) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25206 : oddCount 25206 15 = 5 ∧ acceleratedOrbit 15 25206 = 187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25206 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25206) = 3 ^ 5 * m + 187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25206.1, data_15_25206.2]

/-- Complete interval computation for depth 15, residue 25207. -/
theorem bounds_15_25207 : exactInterval 15 25207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25207 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25207) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25207 : oddCount 25207 15 = 5 ∧ acceleratedOrbit 15 25207 = 187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25207 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25207) = 3 ^ 5 * m + 187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25207.1, data_15_25207.2]

/-- Complete interval computation for depth 15, residue 25208. -/
theorem bounds_15_25208 : exactInterval 15 25208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25208 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25208) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25208 : oddCount 25208 15 = 5 ∧ acceleratedOrbit 15 25208 = 187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25208 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25208) = 3 ^ 5 * m + 187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25208.1, data_15_25208.2]

/-- Complete interval computation for depth 15, residue 25209. -/
theorem bounds_15_25209 : exactInterval 15 25209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25209 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25209) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25209 : oddCount 25209 15 = 9 ∧ acceleratedOrbit 15 25209 = 15146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25209 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25209) = 3 ^ 9 * m + 15146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25209.1, data_15_25209.2]

/-- Complete interval computation for depth 15, residue 25210. -/
theorem bounds_15_25210 : exactInterval 15 25210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25210 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25210) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25210 : oddCount 25210 15 = 5 ∧ acceleratedOrbit 15 25210 = 187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25210 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25210) = 3 ^ 5 * m + 187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25210.1, data_15_25210.2]

/-- Complete interval computation for depth 15, residue 25211. -/
theorem bounds_15_25211 : exactInterval 15 25211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25211 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25211) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25211 : oddCount 25211 15 = 10 ∧ acceleratedOrbit 15 25211 = 45440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25211 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25211) = 3 ^ 10 * m + 45440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25211.1, data_15_25211.2]

/-- Complete interval computation for depth 15, residue 25212. -/
theorem bounds_15_25212 : exactInterval 15 25212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25212 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25212) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25212 : oddCount 25212 15 = 12 ∧ acceleratedOrbit 15 25212 = 408968 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25212 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25212) = 3 ^ 12 * m + 408968 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25212.1, data_15_25212.2]

/-- Complete interval computation for depth 15, residue 25213. -/
theorem bounds_15_25213 : exactInterval 15 25213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25213 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25213) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25213 : oddCount 25213 15 = 12 ∧ acceleratedOrbit 15 25213 = 408968 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25213 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25213) = 3 ^ 12 * m + 408968 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25213.1, data_15_25213.2]

/-- Complete interval computation for depth 15, residue 25214. -/
theorem bounds_15_25214 : exactInterval 15 25214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25214 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25214) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25214 : oddCount 25214 15 = 12 ∧ acceleratedOrbit 15 25214 = 408968 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25214 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25214) = 3 ^ 12 * m + 408968 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25214.1, data_15_25214.2]

/-- Complete interval computation for depth 15, residue 25215. -/
theorem bounds_15_25215 : exactInterval 15 25215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25215 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25215) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25215 : oddCount 25215 15 = 12 ∧ acceleratedOrbit 15 25215 = 408962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25215 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25215) = 3 ^ 12 * m + 408962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25215.1, data_15_25215.2]

/-- Complete interval computation for depth 15, residue 25216. -/
theorem bounds_15_25216 : exactInterval 15 25216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25216 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25216) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25216 : oddCount 25216 15 = 2 ∧ acceleratedOrbit 15 25216 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25216 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25216) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25216.1, data_15_25216.2]

/-- Complete interval computation for depth 15, residue 25217. -/
theorem bounds_15_25217 : exactInterval 15 25217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25217 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25217) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25217 : oddCount 25217 15 = 8 ∧ acceleratedOrbit 15 25217 = 5050 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25217 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25217) = 3 ^ 8 * m + 5050 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25217.1, data_15_25217.2]

/-- Complete interval computation for depth 15, residue 25218. -/
theorem bounds_15_25218 : exactInterval 15 25218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25218 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25218) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25218 : oddCount 25218 15 = 6 ∧ acceleratedOrbit 15 25218 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25218 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25218) = 3 ^ 6 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25218.1, data_15_25218.2]

/-- Complete interval computation for depth 15, residue 25219. -/
theorem bounds_15_25219 : exactInterval 15 25219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25219 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25219) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25219 : oddCount 25219 15 = 6 ∧ acceleratedOrbit 15 25219 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25219 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25219) = 3 ^ 6 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25219.1, data_15_25219.2]

/-- Complete interval computation for depth 15, residue 25220. -/
theorem bounds_15_25220 : exactInterval 15 25220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25220 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25220) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25220 : oddCount 25220 15 = 7 ∧ acceleratedOrbit 15 25220 = 1684 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25220 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25220) = 3 ^ 7 * m + 1684 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25220.1, data_15_25220.2]

/-- Complete interval computation for depth 15, residue 25221. -/
theorem bounds_15_25221 : exactInterval 15 25221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25221 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25221) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25221 : oddCount 25221 15 = 7 ∧ acceleratedOrbit 15 25221 = 1684 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25221 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25221) = 3 ^ 7 * m + 1684 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25221.1, data_15_25221.2]

/-- Complete interval computation for depth 15, residue 25222. -/
theorem bounds_15_25222 : exactInterval 15 25222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25222 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25222) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25222 : oddCount 25222 15 = 7 ∧ acceleratedOrbit 15 25222 = 1684 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25222 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25222) = 3 ^ 7 * m + 1684 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25222.1, data_15_25222.2]

/-- Complete interval computation for depth 15, residue 25223. -/
theorem bounds_15_25223 : exactInterval 15 25223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25223 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25223) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25223 : oddCount 25223 15 = 7 ∧ acceleratedOrbit 15 25223 = 1684 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25223 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25223) = 3 ^ 7 * m + 1684 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25223.1, data_15_25223.2]

/-- Complete interval computation for depth 15, residue 25224. -/
theorem bounds_15_25224 : exactInterval 15 25224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25224 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25224) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25224 : oddCount 25224 15 = 6 ∧ acceleratedOrbit 15 25224 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25224 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25224) = 3 ^ 6 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25224.1, data_15_25224.2]

/-- Complete interval computation for depth 15, residue 25225. -/
theorem bounds_15_25225 : exactInterval 15 25225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25225 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25225) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25225 : oddCount 25225 15 = 10 ∧ acceleratedOrbit 15 25225 = 45461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25225 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25225) = 3 ^ 10 * m + 45461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25225.1, data_15_25225.2]

/-- Complete interval computation for depth 15, residue 25226. -/
theorem bounds_15_25226 : exactInterval 15 25226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25226 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25226) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25226 : oddCount 25226 15 = 6 ∧ acceleratedOrbit 15 25226 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25226 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25226) = 3 ^ 6 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25226.1, data_15_25226.2]

/-- Complete interval computation for depth 15, residue 25227. -/
theorem bounds_15_25227 : exactInterval 15 25227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25227 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25227) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25227 : oddCount 25227 15 = 7 ∧ acceleratedOrbit 15 25227 = 1684 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25227 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25227) = 3 ^ 7 * m + 1684 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25227.1, data_15_25227.2]

/-- Complete interval computation for depth 15, residue 25228. -/
theorem bounds_15_25228 : exactInterval 15 25228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25228 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25228) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25228 : oddCount 25228 15 = 6 ∧ acceleratedOrbit 15 25228 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25228 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25228) = 3 ^ 6 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25228.1, data_15_25228.2]

/-- Complete interval computation for depth 15, residue 25229. -/
theorem bounds_15_25229 : exactInterval 15 25229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25229 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25229) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25229 : oddCount 25229 15 = 6 ∧ acceleratedOrbit 15 25229 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25229 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25229) = 3 ^ 6 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25229.1, data_15_25229.2]

/-- Complete interval computation for depth 15, residue 25230. -/
theorem bounds_15_25230 : exactInterval 15 25230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25230 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25230) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25230 : oddCount 25230 15 = 9 ∧ acceleratedOrbit 15 25230 = 15157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25230 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25230) = 3 ^ 9 * m + 15157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25230.1, data_15_25230.2]

end Collatz.Research.PassageAtlas.Batch0770
