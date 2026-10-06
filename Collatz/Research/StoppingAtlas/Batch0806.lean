import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0806

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5196. -/
theorem bounds_13_5196 : exactInterval 13 5196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5196 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5196) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5196 : oddCount 5196 13 = 7 ∧ acceleratedOrbit 13 5196 = 1390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5196 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5196) = 3 ^ 7 * m + 1390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5196.1, data_13_5196.2]

/-- Complete interval computation for depth 13, residue 5197. -/
theorem bounds_13_5197 : exactInterval 13 5197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5197 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5197) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5197 : oddCount 5197 13 = 7 ∧ acceleratedOrbit 13 5197 = 1390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5197 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5197) = 3 ^ 7 * m + 1390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5197.1, data_13_5197.2]

/-- Complete interval computation for depth 13, residue 5198. -/
theorem bounds_13_5198 : exactInterval 13 5198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5198 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5198) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5198 : oddCount 5198 13 = 6 ∧ acceleratedOrbit 13 5198 = 463 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5198 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5198) = 3 ^ 6 * m + 463 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5198.1, data_13_5198.2]

/-- Complete interval computation for depth 13, residue 5199. -/
theorem bounds_13_5199 : exactInterval 13 5199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5199 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5199) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5199 : oddCount 5199 13 = 6 ∧ acceleratedOrbit 13 5199 = 463 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5199 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5199) = 3 ^ 6 * m + 463 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5199.1, data_13_5199.2]

/-- Complete interval computation for depth 13, residue 5200. -/
theorem bounds_13_5200 : exactInterval 13 5200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5200 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5200) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5200 : oddCount 5200 13 = 4 ∧ acceleratedOrbit 13 5200 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5200 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5200) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5200.1, data_13_5200.2]

/-- Complete interval computation for depth 13, residue 5201. -/
theorem bounds_13_5201 : exactInterval 13 5201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5201 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5201) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5201 : oddCount 5201 13 = 7 ∧ acceleratedOrbit 13 5201 = 1390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5201 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5201) = 3 ^ 7 * m + 1390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5201.1, data_13_5201.2]

/-- Complete interval computation for depth 13, residue 5202. -/
theorem bounds_13_5202 : exactInterval 13 5202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5202 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5202) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5202 : oddCount 5202 13 = 8 ∧ acceleratedOrbit 13 5202 = 4169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5202 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5202) = 3 ^ 8 * m + 4169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5202.1, data_13_5202.2]

/-- Complete interval computation for depth 13, residue 5203. -/
theorem bounds_13_5203 : exactInterval 13 5203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5203 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5203) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5203 : oddCount 5203 13 = 8 ∧ acceleratedOrbit 13 5203 = 4169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5203 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5203) = 3 ^ 8 * m + 4169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5203.1, data_13_5203.2]

/-- Complete interval computation for depth 13, residue 5204. -/
theorem bounds_13_5204 : exactInterval 13 5204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5204 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5204) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5204 : oddCount 5204 13 = 4 ∧ acceleratedOrbit 13 5204 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5204 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5204) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5204.1, data_13_5204.2]

/-- Complete interval computation for depth 13, residue 5205. -/
theorem bounds_13_5205 : exactInterval 13 5205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5205 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5205) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5205 : oddCount 5205 13 = 4 ∧ acceleratedOrbit 13 5205 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5205 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5205) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5205.1, data_13_5205.2]

/-- Complete interval computation for depth 13, residue 5206. -/
theorem bounds_13_5206 : exactInterval 13 5206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5206 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5206) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5206 : oddCount 5206 13 = 5 ∧ acceleratedOrbit 13 5206 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5206 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5206) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5206.1, data_13_5206.2]

/-- Complete interval computation for depth 13, residue 5207. -/
theorem bounds_13_5207 : exactInterval 13 5207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5207 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5207) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5207 : oddCount 5207 13 = 5 ∧ acceleratedOrbit 13 5207 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5207 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5207) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5207.1, data_13_5207.2]

/-- Complete interval computation for depth 13, residue 5208. -/
theorem bounds_13_5208 : exactInterval 13 5208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5208 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5208) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5208 : oddCount 5208 13 = 5 ∧ acceleratedOrbit 13 5208 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5208 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5208) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5208.1, data_13_5208.2]

/-- Complete interval computation for depth 13, residue 5209. -/
theorem bounds_13_5209 : exactInterval 13 5209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5209 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5209) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5209 : oddCount 5209 13 = 6 ∧ acceleratedOrbit 13 5209 = 464 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5209 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5209) = 3 ^ 6 * m + 464 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5209.1, data_13_5209.2]

/-- Complete interval computation for depth 13, residue 5210. -/
theorem bounds_13_5210 : exactInterval 13 5210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5210 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5210) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5210 : oddCount 5210 13 = 5 ∧ acceleratedOrbit 13 5210 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5210 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5210) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5210.1, data_13_5210.2]

/-- Complete interval computation for depth 13, residue 5211. -/
theorem bounds_13_5211 : exactInterval 13 5211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5211 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5211) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5211 : oddCount 5211 13 = 10 ∧ acceleratedOrbit 13 5211 = 37574 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5211 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5211) = 3 ^ 10 * m + 37574 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5211.1, data_13_5211.2]

end Collatz.Research.StoppingAtlas.Batch0806
