import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0611

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2201. -/
theorem bounds_13_2201 : exactInterval 13 2201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2201 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2201) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2201 : oddCount 2201 13 = 7 ∧ acceleratedOrbit 13 2201 = 589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2201 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2201) = 3 ^ 7 * m + 589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2201.1, data_13_2201.2]

/-- Complete interval computation for depth 13, residue 2202. -/
theorem bounds_13_2202 : exactInterval 13 2202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2202 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2202) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2202 : oddCount 2202 13 = 7 ∧ acceleratedOrbit 13 2202 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2202 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2202) = 3 ^ 7 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2202.1, data_13_2202.2]

/-- Complete interval computation for depth 13, residue 2203. -/
theorem bounds_13_2203 : exactInterval 13 2203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2203 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2203) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2203 : oddCount 2203 13 = 8 ∧ acceleratedOrbit 13 2203 = 1766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2203 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2203) = 3 ^ 8 * m + 1766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2203.1, data_13_2203.2]

/-- Complete interval computation for depth 13, residue 2204. -/
theorem bounds_13_2204 : exactInterval 13 2204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2204 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2204) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2204 : oddCount 2204 13 = 6 ∧ acceleratedOrbit 13 2204 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2204 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2204) = 3 ^ 6 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2204.1, data_13_2204.2]

/-- Complete interval computation for depth 13, residue 2205. -/
theorem bounds_13_2205 : exactInterval 13 2205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2205 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2205) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2205 : oddCount 2205 13 = 6 ∧ acceleratedOrbit 13 2205 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2205 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2205) = 3 ^ 6 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2205.1, data_13_2205.2]

/-- Complete interval computation for depth 13, residue 2206. -/
theorem bounds_13_2206 : exactInterval 13 2206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2206 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2206) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2206 : oddCount 2206 13 = 6 ∧ acceleratedOrbit 13 2206 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2206 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2206) = 3 ^ 6 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2206.1, data_13_2206.2]

/-- Complete interval computation for depth 13, residue 2207. -/
theorem bounds_13_2207 : exactInterval 13 2207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2207 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2207) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2207 : oddCount 2207 13 = 11 ∧ acceleratedOrbit 13 2207 = 47749 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2207 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2207) = 3 ^ 11 * m + 47749 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2207.1, data_13_2207.2]

/-- Complete interval computation for depth 13, residue 2208. -/
theorem bounds_13_2208 : exactInterval 13 2208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2208 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2208) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2208 : oddCount 2208 13 = 3 ∧ acceleratedOrbit 13 2208 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2208 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2208) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2208.1, data_13_2208.2]

/-- Complete interval computation for depth 13, residue 2209. -/
theorem bounds_13_2209 : exactInterval 13 2209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2209 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2209) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2209 : oddCount 2209 13 = 8 ∧ acceleratedOrbit 13 2209 = 1772 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2209 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2209) = 3 ^ 8 * m + 1772 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2209.1, data_13_2209.2]

/-- Complete interval computation for depth 13, residue 2210. -/
theorem bounds_13_2210 : exactInterval 13 2210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2210 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2210) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2210 : oddCount 2210 13 = 7 ∧ acceleratedOrbit 13 2210 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2210 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2210) = 3 ^ 7 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2210.1, data_13_2210.2]

/-- Complete interval computation for depth 13, residue 2211. -/
theorem bounds_13_2211 : exactInterval 13 2211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2211 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2211) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2211 : oddCount 2211 13 = 7 ∧ acceleratedOrbit 13 2211 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2211 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2211) = 3 ^ 7 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2211.1, data_13_2211.2]

/-- Complete interval computation for depth 13, residue 2212. -/
theorem bounds_13_2212 : exactInterval 13 2212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2212 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2212) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2212 : oddCount 2212 13 = 8 ∧ acceleratedOrbit 13 2212 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2212 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2212) = 3 ^ 8 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2212.1, data_13_2212.2]

/-- Complete interval computation for depth 13, residue 2213. -/
theorem bounds_13_2213 : exactInterval 13 2213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2213 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2213) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2213 : oddCount 2213 13 = 8 ∧ acceleratedOrbit 13 2213 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2213 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2213) = 3 ^ 8 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2213.1, data_13_2213.2]

/-- Complete interval computation for depth 13, residue 2214. -/
theorem bounds_13_2214 : exactInterval 13 2214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2214 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2214) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2214 : oddCount 2214 13 = 8 ∧ acceleratedOrbit 13 2214 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2214 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2214) = 3 ^ 8 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2214.1, data_13_2214.2]

/-- Complete interval computation for depth 13, residue 2215. -/
theorem bounds_13_2215 : exactInterval 13 2215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2215 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2215) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2215 : oddCount 2215 13 = 10 ∧ acceleratedOrbit 13 2215 = 15977 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2215 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2215) = 3 ^ 10 * m + 15977 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2215.1, data_13_2215.2]

end Collatz.Research.StoppingAtlas.Batch0611
