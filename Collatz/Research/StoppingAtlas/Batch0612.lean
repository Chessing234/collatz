import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0612

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2216. -/
theorem bounds_13_2216 : exactInterval 13 2216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2216 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2216) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2216 : oddCount 2216 13 = 3 ∧ acceleratedOrbit 13 2216 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2216 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2216) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2216.1, data_13_2216.2]

/-- Complete interval computation for depth 13, residue 2217. -/
theorem bounds_13_2217 : exactInterval 13 2217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2217 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2217) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2217 : oddCount 2217 13 = 11 ∧ acceleratedOrbit 13 2217 = 47978 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2217 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2217) = 3 ^ 11 * m + 47978 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2217.1, data_13_2217.2]

/-- Complete interval computation for depth 13, residue 2218. -/
theorem bounds_13_2218 : exactInterval 13 2218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2218 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2218) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2218 : oddCount 2218 13 = 3 ∧ acceleratedOrbit 13 2218 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2218 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2218) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2218.1, data_13_2218.2]

/-- Complete interval computation for depth 13, residue 2219. -/
theorem bounds_13_2219 : exactInterval 13 2219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2219 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2219) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2219 : oddCount 2219 13 = 8 ∧ acceleratedOrbit 13 2219 = 1781 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2219 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2219) = 3 ^ 8 * m + 1781 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2219.1, data_13_2219.2]

/-- Complete interval computation for depth 13, residue 2220. -/
theorem bounds_13_2220 : exactInterval 13 2220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2220 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2220) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2220 : oddCount 2220 13 = 4 ∧ acceleratedOrbit 13 2220 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2220 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2220) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2220.1, data_13_2220.2]

/-- Complete interval computation for depth 13, residue 2221. -/
theorem bounds_13_2221 : exactInterval 13 2221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2221 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2221) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2221 : oddCount 2221 13 = 4 ∧ acceleratedOrbit 13 2221 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2221 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2221) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2221.1, data_13_2221.2]

/-- Complete interval computation for depth 13, residue 2222. -/
theorem bounds_13_2222 : exactInterval 13 2222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2222 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2222) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2222 : oddCount 2222 13 = 4 ∧ acceleratedOrbit 13 2222 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2222 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2222) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2222.1, data_13_2222.2]

/-- Complete interval computation for depth 13, residue 2223. -/
theorem bounds_13_2223 : exactInterval 13 2223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2223 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2223) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2223 : oddCount 2223 13 = 10 ∧ acceleratedOrbit 13 2223 = 16037 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2223 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2223) = 3 ^ 10 * m + 16037 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2223.1, data_13_2223.2]

/-- Complete interval computation for depth 13, residue 2224. -/
theorem bounds_13_2224 : exactInterval 13 2224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2224 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2224) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2224 : oddCount 2224 13 = 5 ∧ acceleratedOrbit 13 2224 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2224 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2224) = 3 ^ 5 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2224.1, data_13_2224.2]

/-- Complete interval computation for depth 13, residue 2225. -/
theorem bounds_13_2225 : exactInterval 13 2225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2225 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2225) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2225 : oddCount 2225 13 = 6 ∧ acceleratedOrbit 13 2225 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2225 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2225) = 3 ^ 6 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2225.1, data_13_2225.2]

/-- Complete interval computation for depth 13, residue 2226. -/
theorem bounds_13_2226 : exactInterval 13 2226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2226 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2226) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2226 : oddCount 2226 13 = 6 ∧ acceleratedOrbit 13 2226 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2226 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2226) = 3 ^ 6 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2226.1, data_13_2226.2]

/-- Complete interval computation for depth 13, residue 2227. -/
theorem bounds_13_2227 : exactInterval 13 2227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2227 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2227) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2227 : oddCount 2227 13 = 6 ∧ acceleratedOrbit 13 2227 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2227 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2227) = 3 ^ 6 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2227.1, data_13_2227.2]

/-- Complete interval computation for depth 13, residue 2228. -/
theorem bounds_13_2228 : exactInterval 13 2228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2228 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2228) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2228 : oddCount 2228 13 = 5 ∧ acceleratedOrbit 13 2228 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2228 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2228) = 3 ^ 5 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2228.1, data_13_2228.2]

/-- Complete interval computation for depth 13, residue 2229. -/
theorem bounds_13_2229 : exactInterval 13 2229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2229 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2229) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2229 : oddCount 2229 13 = 5 ∧ acceleratedOrbit 13 2229 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2229 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2229) = 3 ^ 5 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2229.1, data_13_2229.2]

/-- Complete interval computation for depth 13, residue 2230. -/
theorem bounds_13_2230 : exactInterval 13 2230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2230 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2230) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2230 : oddCount 2230 13 = 9 ∧ acceleratedOrbit 13 2230 = 5366 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2230 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2230) = 3 ^ 9 * m + 5366 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2230.1, data_13_2230.2]

/-- Complete interval computation for depth 13, residue 2231. -/
theorem bounds_13_2231 : exactInterval 13 2231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2231 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2231) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2231 : oddCount 2231 13 = 9 ∧ acceleratedOrbit 13 2231 = 5366 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2231 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2231) = 3 ^ 9 * m + 5366 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2231.1, data_13_2231.2]

end Collatz.Research.StoppingAtlas.Batch0612
