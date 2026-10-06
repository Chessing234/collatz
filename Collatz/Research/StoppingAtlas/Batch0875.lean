import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0875

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6256. -/
theorem bounds_13_6256 : exactInterval 13 6256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6256 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6256) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6256 : oddCount 6256 13 = 4 ∧ acceleratedOrbit 13 6256 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6256 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6256) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6256.1, data_13_6256.2]

/-- Complete interval computation for depth 13, residue 6257. -/
theorem bounds_13_6257 : exactInterval 13 6257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6257 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6257) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6257 : oddCount 6257 13 = 5 ∧ acceleratedOrbit 13 6257 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6257 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6257) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6257.1, data_13_6257.2]

/-- Complete interval computation for depth 13, residue 6258. -/
theorem bounds_13_6258 : exactInterval 13 6258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6258 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6258) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6258 : oddCount 6258 13 = 7 ∧ acceleratedOrbit 13 6258 = 1673 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6258 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6258) = 3 ^ 7 * m + 1673 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6258.1, data_13_6258.2]

/-- Complete interval computation for depth 13, residue 6259. -/
theorem bounds_13_6259 : exactInterval 13 6259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6259 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6259) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6259 : oddCount 6259 13 = 7 ∧ acceleratedOrbit 13 6259 = 1673 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6259 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6259) = 3 ^ 7 * m + 1673 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6259.1, data_13_6259.2]

/-- Complete interval computation for depth 13, residue 6260. -/
theorem bounds_13_6260 : exactInterval 13 6260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6260 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6260) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6260 : oddCount 6260 13 = 4 ∧ acceleratedOrbit 13 6260 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6260 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6260) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6260.1, data_13_6260.2]

/-- Complete interval computation for depth 13, residue 6261. -/
theorem bounds_13_6261 : exactInterval 13 6261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6261 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6261) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6261 : oddCount 6261 13 = 4 ∧ acceleratedOrbit 13 6261 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6261 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6261) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6261.1, data_13_6261.2]

/-- Complete interval computation for depth 13, residue 6262. -/
theorem bounds_13_6262 : exactInterval 13 6262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6262 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6262) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6262 : oddCount 6262 13 = 8 ∧ acceleratedOrbit 13 6262 = 5021 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6262 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6262) = 3 ^ 8 * m + 5021 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6262.1, data_13_6262.2]

/-- Complete interval computation for depth 13, residue 6263. -/
theorem bounds_13_6263 : exactInterval 13 6263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6263 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6263) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6263 : oddCount 6263 13 = 8 ∧ acceleratedOrbit 13 6263 = 5021 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6263 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6263) = 3 ^ 8 * m + 5021 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6263.1, data_13_6263.2]

/-- Complete interval computation for depth 13, residue 6264. -/
theorem bounds_13_6264 : exactInterval 13 6264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6264 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6264) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6264 : oddCount 6264 13 = 4 ∧ acceleratedOrbit 13 6264 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6264 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6264) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6264.1, data_13_6264.2]

/-- Complete interval computation for depth 13, residue 6265. -/
theorem bounds_13_6265 : exactInterval 13 6265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6265 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6265) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6265 : oddCount 6265 13 = 9 ∧ acceleratedOrbit 13 6265 = 15059 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6265 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6265) = 3 ^ 9 * m + 15059 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6265.1, data_13_6265.2]

/-- Complete interval computation for depth 13, residue 6266. -/
theorem bounds_13_6266 : exactInterval 13 6266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6266 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6266) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6266 : oddCount 6266 13 = 4 ∧ acceleratedOrbit 13 6266 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6266 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6266) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6266.1, data_13_6266.2]

/-- Complete interval computation for depth 13, residue 6267. -/
theorem bounds_13_6267 : exactInterval 13 6267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6267 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6267) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6267 : oddCount 6267 13 = 9 ∧ acceleratedOrbit 13 6267 = 15065 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6267 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6267) = 3 ^ 9 * m + 15065 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6267.1, data_13_6267.2]

/-- Complete interval computation for depth 13, residue 6268. -/
theorem bounds_13_6268 : exactInterval 13 6268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6268 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6268) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6268 : oddCount 6268 13 = 8 ∧ acceleratedOrbit 13 6268 = 5024 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6268 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6268) = 3 ^ 8 * m + 5024 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6268.1, data_13_6268.2]

/-- Complete interval computation for depth 13, residue 6269. -/
theorem bounds_13_6269 : exactInterval 13 6269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6269 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6269) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6269 : oddCount 6269 13 = 8 ∧ acceleratedOrbit 13 6269 = 5024 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6269 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6269) = 3 ^ 8 * m + 5024 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6269.1, data_13_6269.2]

/-- Complete interval computation for depth 13, residue 6270. -/
theorem bounds_13_6270 : exactInterval 13 6270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6270 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6270) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6270 : oddCount 6270 13 = 8 ∧ acceleratedOrbit 13 6270 = 5024 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6270 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6270) = 3 ^ 8 * m + 5024 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6270.1, data_13_6270.2]

/-- Complete interval computation for depth 13, residue 6271. -/
theorem bounds_13_6271 : exactInterval 13 6271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6271 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6271) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6271 : oddCount 6271 13 = 9 ∧ acceleratedOrbit 13 6271 = 15070 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6271 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6271) = 3 ^ 9 * m + 15070 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6271.1, data_13_6271.2]

end Collatz.Research.StoppingAtlas.Batch0875
