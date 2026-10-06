import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0873

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6225. -/
theorem bounds_13_6225 : exactInterval 13 6225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6225 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6225) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6225 : oddCount 6225 13 = 7 ∧ acceleratedOrbit 13 6225 = 1664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6225 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6225) = 3 ^ 7 * m + 1664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6225.1, data_13_6225.2]

/-- Complete interval computation for depth 13, residue 6226. -/
theorem bounds_13_6226 : exactInterval 13 6226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6226 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6226) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6226 : oddCount 6226 13 = 7 ∧ acceleratedOrbit 13 6226 = 1663 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6226 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6226) = 3 ^ 7 * m + 1663 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6226.1, data_13_6226.2]

/-- Complete interval computation for depth 13, residue 6227. -/
theorem bounds_13_6227 : exactInterval 13 6227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6227 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6227) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6227 : oddCount 6227 13 = 7 ∧ acceleratedOrbit 13 6227 = 1663 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6227 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6227) = 3 ^ 7 * m + 1663 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6227.1, data_13_6227.2]

/-- Complete interval computation for depth 13, residue 6228. -/
theorem bounds_13_6228 : exactInterval 13 6228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6228 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6228) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6228 : oddCount 6228 13 = 5 ∧ acceleratedOrbit 13 6228 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6228 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6228) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6228.1, data_13_6228.2]

/-- Complete interval computation for depth 13, residue 6229. -/
theorem bounds_13_6229 : exactInterval 13 6229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6229 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6229) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6229 : oddCount 6229 13 = 5 ∧ acceleratedOrbit 13 6229 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6229 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6229) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6229.1, data_13_6229.2]

/-- Complete interval computation for depth 13, residue 6230. -/
theorem bounds_13_6230 : exactInterval 13 6230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6230 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6230) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6230 : oddCount 6230 13 = 5 ∧ acceleratedOrbit 13 6230 = 185 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6230 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6230) = 3 ^ 5 * m + 185 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6230.1, data_13_6230.2]

/-- Complete interval computation for depth 13, residue 6231. -/
theorem bounds_13_6231 : exactInterval 13 6231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6231 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6231) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6231 : oddCount 6231 13 = 5 ∧ acceleratedOrbit 13 6231 = 185 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6231 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6231) = 3 ^ 5 * m + 185 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6231.1, data_13_6231.2]

/-- Complete interval computation for depth 13, residue 6232. -/
theorem bounds_13_6232 : exactInterval 13 6232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6232 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6232) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6232 : oddCount 6232 13 = 6 ∧ acceleratedOrbit 13 6232 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6232 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6232) = 3 ^ 6 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6232.1, data_13_6232.2]

/-- Complete interval computation for depth 13, residue 6233. -/
theorem bounds_13_6233 : exactInterval 13 6233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6233 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6233) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6233 : oddCount 6233 13 = 5 ∧ acceleratedOrbit 13 6233 = 185 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6233 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6233) = 3 ^ 5 * m + 185 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6233.1, data_13_6233.2]

/-- Complete interval computation for depth 13, residue 6234. -/
theorem bounds_13_6234 : exactInterval 13 6234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6234 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6234) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6234 : oddCount 6234 13 = 6 ∧ acceleratedOrbit 13 6234 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6234 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6234) = 3 ^ 6 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6234.1, data_13_6234.2]

/-- Complete interval computation for depth 13, residue 6235. -/
theorem bounds_13_6235 : exactInterval 13 6235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6235 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6235) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6235 : oddCount 6235 13 = 11 ∧ acceleratedOrbit 13 6235 = 134864 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6235 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6235) = 3 ^ 11 * m + 134864 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6235.1, data_13_6235.2]

/-- Complete interval computation for depth 13, residue 6236. -/
theorem bounds_13_6236 : exactInterval 13 6236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6236 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6236) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6236 : oddCount 6236 13 = 6 ∧ acceleratedOrbit 13 6236 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6236 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6236) = 3 ^ 6 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6236.1, data_13_6236.2]

/-- Complete interval computation for depth 13, residue 6237. -/
theorem bounds_13_6237 : exactInterval 13 6237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6237 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6237) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6237 : oddCount 6237 13 = 6 ∧ acceleratedOrbit 13 6237 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6237 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6237) = 3 ^ 6 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6237.1, data_13_6237.2]

/-- Complete interval computation for depth 13, residue 6238. -/
theorem bounds_13_6238 : exactInterval 13 6238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6238 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6238) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6238 : oddCount 6238 13 = 7 ∧ acceleratedOrbit 13 6238 = 1666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6238 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6238) = 3 ^ 7 * m + 1666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6238.1, data_13_6238.2]

/-- Complete interval computation for depth 13, residue 6239. -/
theorem bounds_13_6239 : exactInterval 13 6239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6239 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6239) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6239 : oddCount 6239 13 = 7 ∧ acceleratedOrbit 13 6239 = 1666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6239 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6239) = 3 ^ 7 * m + 1666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6239.1, data_13_6239.2]

/-- Complete interval computation for depth 13, residue 6240. -/
theorem bounds_13_6240 : exactInterval 13 6240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6240 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6240) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6240 : oddCount 6240 13 = 5 ∧ acceleratedOrbit 13 6240 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6240 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6240) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6240.1, data_13_6240.2]

end Collatz.Research.StoppingAtlas.Batch0873
