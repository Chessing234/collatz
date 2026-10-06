import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0808

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5227. -/
theorem bounds_13_5227 : exactInterval 13 5227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5227 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5227) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5227 : oddCount 5227 13 = 7 ∧ acceleratedOrbit 13 5227 = 1396 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5227 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5227) = 3 ^ 7 * m + 1396 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5227.1, data_13_5227.2]

/-- Complete interval computation for depth 13, residue 5228. -/
theorem bounds_13_5228 : exactInterval 13 5228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5228 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5228) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5228 : oddCount 5228 13 = 9 ∧ acceleratedOrbit 13 5228 = 12575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5228 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5228) = 3 ^ 9 * m + 12575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5228.1, data_13_5228.2]

/-- Complete interval computation for depth 13, residue 5229. -/
theorem bounds_13_5229 : exactInterval 13 5229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5229 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5229) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5229 : oddCount 5229 13 = 9 ∧ acceleratedOrbit 13 5229 = 12575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5229 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5229) = 3 ^ 9 * m + 12575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5229.1, data_13_5229.2]

/-- Complete interval computation for depth 13, residue 5230. -/
theorem bounds_13_5230 : exactInterval 13 5230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5230 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5230) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5230 : oddCount 5230 13 = 9 ∧ acceleratedOrbit 13 5230 = 12575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5230 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5230) = 3 ^ 9 * m + 12575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5230.1, data_13_5230.2]

/-- Complete interval computation for depth 13, residue 5231. -/
theorem bounds_13_5231 : exactInterval 13 5231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5231 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5231) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5231 : oddCount 5231 13 = 9 ∧ acceleratedOrbit 13 5231 = 12572 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5231 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5231) = 3 ^ 9 * m + 12572 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5231.1, data_13_5231.2]

/-- Complete interval computation for depth 13, residue 5232. -/
theorem bounds_13_5232 : exactInterval 13 5232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5232 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5232) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5232 : oddCount 5232 13 = 7 ∧ acceleratedOrbit 13 5232 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5232 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5232) = 3 ^ 7 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5232.1, data_13_5232.2]

/-- Complete interval computation for depth 13, residue 5233. -/
theorem bounds_13_5233 : exactInterval 13 5233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5233 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5233) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5233 : oddCount 5233 13 = 4 ∧ acceleratedOrbit 13 5233 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5233 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5233) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5233.1, data_13_5233.2]

/-- Complete interval computation for depth 13, residue 5234. -/
theorem bounds_13_5234 : exactInterval 13 5234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5234 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5234) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5234 : oddCount 5234 13 = 7 ∧ acceleratedOrbit 13 5234 = 1399 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5234 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5234) = 3 ^ 7 * m + 1399 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5234.1, data_13_5234.2]

/-- Complete interval computation for depth 13, residue 5235. -/
theorem bounds_13_5235 : exactInterval 13 5235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5235 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5235) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5235 : oddCount 5235 13 = 7 ∧ acceleratedOrbit 13 5235 = 1399 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5235 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5235) = 3 ^ 7 * m + 1399 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5235.1, data_13_5235.2]

/-- Complete interval computation for depth 13, residue 5236. -/
theorem bounds_13_5236 : exactInterval 13 5236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5236 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5236) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5236 : oddCount 5236 13 = 7 ∧ acceleratedOrbit 13 5236 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5236 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5236) = 3 ^ 7 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5236.1, data_13_5236.2]

/-- Complete interval computation for depth 13, residue 5237. -/
theorem bounds_13_5237 : exactInterval 13 5237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5237 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5237) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5237 : oddCount 5237 13 = 7 ∧ acceleratedOrbit 13 5237 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5237 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5237) = 3 ^ 7 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5237.1, data_13_5237.2]

/-- Complete interval computation for depth 13, residue 5238. -/
theorem bounds_13_5238 : exactInterval 13 5238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5238 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5238) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5238 : oddCount 5238 13 = 6 ∧ acceleratedOrbit 13 5238 = 467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5238 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5238) = 3 ^ 6 * m + 467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5238.1, data_13_5238.2]

/-- Complete interval computation for depth 13, residue 5239. -/
theorem bounds_13_5239 : exactInterval 13 5239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5239 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5239) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5239 : oddCount 5239 13 = 6 ∧ acceleratedOrbit 13 5239 = 467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5239 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5239) = 3 ^ 6 * m + 467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5239.1, data_13_5239.2]

/-- Complete interval computation for depth 13, residue 5240. -/
theorem bounds_13_5240 : exactInterval 13 5240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5240 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5240) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5240 : oddCount 5240 13 = 7 ∧ acceleratedOrbit 13 5240 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5240 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5240) = 3 ^ 7 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5240.1, data_13_5240.2]

/-- Complete interval computation for depth 13, residue 5241. -/
theorem bounds_13_5241 : exactInterval 13 5241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5241 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5241) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5241 : oddCount 5241 13 = 9 ∧ acceleratedOrbit 13 5241 = 12599 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5241 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5241) = 3 ^ 9 * m + 12599 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5241.1, data_13_5241.2]

end Collatz.Research.StoppingAtlas.Batch0808
