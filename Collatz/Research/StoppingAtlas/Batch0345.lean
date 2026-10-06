import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0345

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2211. -/
theorem bounds_12_2211 : exactInterval 12 2211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2211 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2211) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2211 : oddCount 2211 12 = 6 ∧ acceleratedOrbit 12 2211 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2211 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2211) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2211.1, data_12_2211.2]

/-- Complete interval computation for depth 12, residue 2212. -/
theorem bounds_12_2212 : exactInterval 12 2212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2212 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2212) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2212 : oddCount 2212 12 = 8 ∧ acceleratedOrbit 12 2212 = 3554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2212 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2212) = 3 ^ 8 * m + 3554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2212.1, data_12_2212.2]

/-- Complete interval computation for depth 12, residue 2213. -/
theorem bounds_12_2213 : exactInterval 12 2213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2213 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2213) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2213 : oddCount 2213 12 = 8 ∧ acceleratedOrbit 12 2213 = 3554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2213 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2213) = 3 ^ 8 * m + 3554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2213.1, data_12_2213.2]

/-- Complete interval computation for depth 12, residue 2214. -/
theorem bounds_12_2214 : exactInterval 12 2214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2214 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2214) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2214 : oddCount 2214 12 = 8 ∧ acceleratedOrbit 12 2214 = 3554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2214 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2214) = 3 ^ 8 * m + 3554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2214.1, data_12_2214.2]

/-- Complete interval computation for depth 12, residue 2215. -/
theorem bounds_12_2215 : exactInterval 12 2215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2215 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2215) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2215 : oddCount 2215 12 = 9 ∧ acceleratedOrbit 12 2215 = 10651 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2215 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2215) = 3 ^ 9 * m + 10651 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2215.1, data_12_2215.2]

/-- Complete interval computation for depth 12, residue 2216. -/
theorem bounds_12_2216 : exactInterval 12 2216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2216 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2216) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2216 : oddCount 2216 12 = 2 ∧ acceleratedOrbit 12 2216 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2216 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2216) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2216.1, data_12_2216.2]

/-- Complete interval computation for depth 12, residue 2217. -/
theorem bounds_12_2217 : exactInterval 12 2217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2217 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2217) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2217 : oddCount 2217 12 = 10 ∧ acceleratedOrbit 12 2217 = 31985 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2217 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2217) = 3 ^ 10 * m + 31985 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2217.1, data_12_2217.2]

/-- Complete interval computation for depth 12, residue 2218. -/
theorem bounds_12_2218 : exactInterval 12 2218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2218 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2218) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2218 : oddCount 2218 12 = 2 ∧ acceleratedOrbit 12 2218 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2218 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2218) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2218.1, data_12_2218.2]

/-- Complete interval computation for depth 12, residue 2219. -/
theorem bounds_12_2219 : exactInterval 12 2219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2219 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2219) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2219 : oddCount 2219 12 = 7 ∧ acceleratedOrbit 12 2219 = 1187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2219 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2219) = 3 ^ 7 * m + 1187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2219.1, data_12_2219.2]

/-- Complete interval computation for depth 12, residue 2220. -/
theorem bounds_12_2220 : exactInterval 12 2220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2220 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2220) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2220 : oddCount 2220 12 = 4 ∧ acceleratedOrbit 12 2220 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2220 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2220) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2220.1, data_12_2220.2]

/-- Complete interval computation for depth 12, residue 2221. -/
theorem bounds_12_2221 : exactInterval 12 2221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2221 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2221) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2221 : oddCount 2221 12 = 4 ∧ acceleratedOrbit 12 2221 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2221 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2221) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2221.1, data_12_2221.2]

/-- Complete interval computation for depth 12, residue 2222. -/
theorem bounds_12_2222 : exactInterval 12 2222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2222 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2222) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2222 : oddCount 2222 12 = 4 ∧ acceleratedOrbit 12 2222 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2222 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2222) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2222.1, data_12_2222.2]

/-- Complete interval computation for depth 12, residue 2223. -/
theorem bounds_12_2223 : exactInterval 12 2223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2223 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2223) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2223 : oddCount 2223 12 = 9 ∧ acceleratedOrbit 12 2223 = 10691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2223 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2223) = 3 ^ 9 * m + 10691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2223.1, data_12_2223.2]

/-- Complete interval computation for depth 12, residue 2224. -/
theorem bounds_12_2224 : exactInterval 12 2224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2224 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2224) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2224 : oddCount 2224 12 = 5 ∧ acceleratedOrbit 12 2224 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2224 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2224) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2224.1, data_12_2224.2]

/-- Complete interval computation for depth 12, residue 2225. -/
theorem bounds_12_2225 : exactInterval 12 2225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2225 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2225) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2225 : oddCount 2225 12 = 6 ∧ acceleratedOrbit 12 2225 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2225 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2225) = 3 ^ 6 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2225.1, data_12_2225.2]

/-- Complete interval computation for depth 12, residue 2226. -/
theorem bounds_12_2226 : exactInterval 12 2226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2226 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2226) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2226 : oddCount 2226 12 = 6 ∧ acceleratedOrbit 12 2226 = 398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2226 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2226) = 3 ^ 6 * m + 398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2226.1, data_12_2226.2]

end Collatz.Research.StoppingAtlas.Batch0345
