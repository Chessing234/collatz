import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0465

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 15204. -/
theorem bounds_15_15204 : exactInterval 15 15204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15204 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15204) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15204 : oddCount 15204 15 = 5 ∧ acceleratedOrbit 15 15204 = 113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15204 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15204) = 3 ^ 5 * m + 113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15204.1, data_15_15204.2]

/-- Complete interval computation for depth 15, residue 15205. -/
theorem bounds_15_15205 : exactInterval 15 15205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15205 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15205) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15205 : oddCount 15205 15 = 5 ∧ acceleratedOrbit 15 15205 = 113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15205 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15205) = 3 ^ 5 * m + 113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15205.1, data_15_15205.2]

/-- Complete interval computation for depth 15, residue 15206. -/
theorem bounds_15_15206 : exactInterval 15 15206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15206 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15206) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15206 : oddCount 15206 15 = 5 ∧ acceleratedOrbit 15 15206 = 113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15206 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15206) = 3 ^ 5 * m + 113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15206.1, data_15_15206.2]

/-- Complete interval computation for depth 15, residue 15207. -/
theorem bounds_15_15207 : exactInterval 15 15207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15207 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15207) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15207 : oddCount 15207 15 = 10 ∧ acceleratedOrbit 15 15207 = 27406 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15207 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15207) = 3 ^ 10 * m + 27406 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15207.1, data_15_15207.2]

/-- Complete interval computation for depth 15, residue 15208. -/
theorem bounds_15_15208 : exactInterval 15 15208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15208 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15208) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15208 : oddCount 15208 15 = 5 ∧ acceleratedOrbit 15 15208 = 113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15208 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15208) = 3 ^ 5 * m + 113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15208.1, data_15_15208.2]

/-- Complete interval computation for depth 15, residue 15209. -/
theorem bounds_15_15209 : exactInterval 15 15209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15209 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15209) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15209 : oddCount 15209 15 = 8 ∧ acceleratedOrbit 15 15209 = 3046 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15209 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15209) = 3 ^ 8 * m + 3046 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15209.1, data_15_15209.2]

/-- Complete interval computation for depth 15, residue 15210. -/
theorem bounds_15_15210 : exactInterval 15 15210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15210 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15210) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15210 : oddCount 15210 15 = 5 ∧ acceleratedOrbit 15 15210 = 113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15210 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15210) = 3 ^ 5 * m + 113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15210.1, data_15_15210.2]

/-- Complete interval computation for depth 15, residue 15211. -/
theorem bounds_15_15211 : exactInterval 15 15211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15211 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15211) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15211 : oddCount 15211 15 = 7 ∧ acceleratedOrbit 15 15211 = 1016 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15211 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15211) = 3 ^ 7 * m + 1016 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15211.1, data_15_15211.2]

/-- Complete interval computation for depth 15, residue 15212. -/
theorem bounds_15_15212 : exactInterval 15 15212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15212 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15212) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15212 : oddCount 15212 15 = 9 ∧ acceleratedOrbit 15 15212 = 9143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15212 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15212) = 3 ^ 9 * m + 9143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15212.1, data_15_15212.2]

/-- Complete interval computation for depth 15, residue 15213. -/
theorem bounds_15_15213 : exactInterval 15 15213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15213 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15213) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15213 : oddCount 15213 15 = 9 ∧ acceleratedOrbit 15 15213 = 9143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15213 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15213) = 3 ^ 9 * m + 9143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15213.1, data_15_15213.2]

/-- Complete interval computation for depth 15, residue 15214. -/
theorem bounds_15_15214 : exactInterval 15 15214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15214 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15214) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15214 : oddCount 15214 15 = 9 ∧ acceleratedOrbit 15 15214 = 9143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15214 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15214) = 3 ^ 9 * m + 9143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15214.1, data_15_15214.2]

/-- Complete interval computation for depth 15, residue 15215. -/
theorem bounds_15_15215 : exactInterval 15 15215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15215 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15215) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15215 : oddCount 15215 15 = 10 ∧ acceleratedOrbit 15 15215 = 27422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15215 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15215) = 3 ^ 10 * m + 27422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15215.1, data_15_15215.2]

/-- Complete interval computation for depth 15, residue 15216. -/
theorem bounds_15_15216 : exactInterval 15 15216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15216 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15216) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15216 : oddCount 15216 15 = 5 ∧ acceleratedOrbit 15 15216 = 113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15216 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15216) = 3 ^ 5 * m + 113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15216.1, data_15_15216.2]

/-- Complete interval computation for depth 15, residue 15217. -/
theorem bounds_15_15217 : exactInterval 15 15217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15217 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15217) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15217 : oddCount 15217 15 = 5 ∧ acceleratedOrbit 15 15217 = 113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15217 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15217) = 3 ^ 5 * m + 113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15217.1, data_15_15217.2]

/-- Complete interval computation for depth 15, residue 15218. -/
theorem bounds_15_15218 : exactInterval 15 15218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15218 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15218) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15218 : oddCount 15218 15 = 5 ∧ acceleratedOrbit 15 15218 = 113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15218 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15218) = 3 ^ 5 * m + 113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15218.1, data_15_15218.2]

/-- Complete interval computation for depth 15, residue 15219. -/
theorem bounds_15_15219 : exactInterval 15 15219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15219 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15219) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15219 : oddCount 15219 15 = 5 ∧ acceleratedOrbit 15 15219 = 113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15219 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15219) = 3 ^ 5 * m + 113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15219.1, data_15_15219.2]

/-- Complete interval computation for depth 15, residue 15220. -/
theorem bounds_15_15220 : exactInterval 15 15220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15220 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15220) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15220 : oddCount 15220 15 = 5 ∧ acceleratedOrbit 15 15220 = 113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15220 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15220) = 3 ^ 5 * m + 113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15220.1, data_15_15220.2]

/-- Complete interval computation for depth 15, residue 15221. -/
theorem bounds_15_15221 : exactInterval 15 15221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15221 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15221) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15221 : oddCount 15221 15 = 5 ∧ acceleratedOrbit 15 15221 = 113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15221 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15221) = 3 ^ 5 * m + 113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15221.1, data_15_15221.2]

/-- Complete interval computation for depth 15, residue 15222. -/
theorem bounds_15_15222 : exactInterval 15 15222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15222 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15222) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15222 : oddCount 15222 15 = 8 ∧ acceleratedOrbit 15 15222 = 3050 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15222 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15222) = 3 ^ 8 * m + 3050 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15222.1, data_15_15222.2]

/-- Complete interval computation for depth 15, residue 15223. -/
theorem bounds_15_15223 : exactInterval 15 15223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15223 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15223) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15223 : oddCount 15223 15 = 8 ∧ acceleratedOrbit 15 15223 = 3050 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15223 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15223) = 3 ^ 8 * m + 3050 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15223.1, data_15_15223.2]

/-- Complete interval computation for depth 15, residue 15224. -/
theorem bounds_15_15224 : exactInterval 15 15224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15224 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15224) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15224 : oddCount 15224 15 = 9 ∧ acceleratedOrbit 15 15224 = 9152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15224 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15224) = 3 ^ 9 * m + 9152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15224.1, data_15_15224.2]

/-- Complete interval computation for depth 15, residue 15225. -/
theorem bounds_15_15225 : exactInterval 15 15225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15225 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15225) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15225 : oddCount 15225 15 = 11 ∧ acceleratedOrbit 15 15225 = 82322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15225 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15225) = 3 ^ 11 * m + 82322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15225.1, data_15_15225.2]

/-- Complete interval computation for depth 15, residue 15226. -/
theorem bounds_15_15226 : exactInterval 15 15226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15226 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15226) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15226 : oddCount 15226 15 = 9 ∧ acceleratedOrbit 15 15226 = 9152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15226 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15226) = 3 ^ 9 * m + 9152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15226.1, data_15_15226.2]

/-- Complete interval computation for depth 15, residue 15227. -/
theorem bounds_15_15227 : exactInterval 15 15227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15227 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15227) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15227 : oddCount 15227 15 = 9 ∧ acceleratedOrbit 15 15227 = 9148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15227 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15227) = 3 ^ 9 * m + 9148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15227.1, data_15_15227.2]

/-- Complete interval computation for depth 15, residue 15228. -/
theorem bounds_15_15228 : exactInterval 15 15228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15228 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15228) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15228 : oddCount 15228 15 = 9 ∧ acceleratedOrbit 15 15228 = 9152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15228 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15228) = 3 ^ 9 * m + 9152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15228.1, data_15_15228.2]

/-- Complete interval computation for depth 15, residue 15229. -/
theorem bounds_15_15229 : exactInterval 15 15229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15229 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15229) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15229 : oddCount 15229 15 = 9 ∧ acceleratedOrbit 15 15229 = 9152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15229 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15229) = 3 ^ 9 * m + 9152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15229.1, data_15_15229.2]

/-- Complete interval computation for depth 15, residue 15230. -/
theorem bounds_15_15230 : exactInterval 15 15230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15230 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15230) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15230 : oddCount 15230 15 = 12 ∧ acceleratedOrbit 15 15230 = 247040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15230 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15230) = 3 ^ 12 * m + 247040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15230.1, data_15_15230.2]

/-- Complete interval computation for depth 15, residue 15231. -/
theorem bounds_15_15231 : exactInterval 15 15231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15231 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15231) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15231 : oddCount 15231 15 = 12 ∧ acceleratedOrbit 15 15231 = 247040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15231 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15231) = 3 ^ 12 * m + 247040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15231.1, data_15_15231.2]

/-- Complete interval computation for depth 15, residue 15232. -/
theorem bounds_15_15232 : exactInterval 15 15232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15232 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15232) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15232 : oddCount 15232 15 = 4 ∧ acceleratedOrbit 15 15232 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15232 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15232) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15232.1, data_15_15232.2]

/-- Complete interval computation for depth 15, residue 15233. -/
theorem bounds_15_15233 : exactInterval 15 15233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15233 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15233) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15233 : oddCount 15233 15 = 11 ∧ acceleratedOrbit 15 15233 = 82376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15233 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15233) = 3 ^ 11 * m + 82376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15233.1, data_15_15233.2]

/-- Complete interval computation for depth 15, residue 15234. -/
theorem bounds_15_15234 : exactInterval 15 15234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15234 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15234) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15234 : oddCount 15234 15 = 8 ∧ acceleratedOrbit 15 15234 = 3053 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15234 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15234) = 3 ^ 8 * m + 3053 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15234.1, data_15_15234.2]

/-- Complete interval computation for depth 15, residue 15235. -/
theorem bounds_15_15235 : exactInterval 15 15235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15235 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15235) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15235 : oddCount 15235 15 = 8 ∧ acceleratedOrbit 15 15235 = 3053 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15235 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15235) = 3 ^ 8 * m + 3053 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15235.1, data_15_15235.2]

/-- Complete interval computation for depth 15, residue 15236. -/
theorem bounds_15_15236 : exactInterval 15 15236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15236 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15236) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15236 : oddCount 15236 15 = 8 ∧ acceleratedOrbit 15 15236 = 3053 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15236 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15236) = 3 ^ 8 * m + 3053 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15236.1, data_15_15236.2]

end Collatz.Research.PassageAtlas.Batch0465
