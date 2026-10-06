import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0881

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6348. -/
theorem bounds_13_6348 : exactInterval 13 6348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6348 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6348) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6348 : oddCount 6348 13 = 7 ∧ acceleratedOrbit 13 6348 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6348 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6348) = 3 ^ 7 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6348.1, data_13_6348.2]

/-- Complete interval computation for depth 13, residue 6349. -/
theorem bounds_13_6349 : exactInterval 13 6349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6349 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6349) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6349 : oddCount 6349 13 = 7 ∧ acceleratedOrbit 13 6349 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6349 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6349) = 3 ^ 7 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6349.1, data_13_6349.2]

/-- Complete interval computation for depth 13, residue 6350. -/
theorem bounds_13_6350 : exactInterval 13 6350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6350 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6350) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6350 : oddCount 6350 13 = 10 ∧ acceleratedOrbit 13 6350 = 45791 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6350 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6350) = 3 ^ 10 * m + 45791 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6350.1, data_13_6350.2]

/-- Complete interval computation for depth 13, residue 6351. -/
theorem bounds_13_6351 : exactInterval 13 6351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6351 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6351) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6351 : oddCount 6351 13 = 10 ∧ acceleratedOrbit 13 6351 = 45791 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6351 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6351) = 3 ^ 10 * m + 45791 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6351.1, data_13_6351.2]

/-- Complete interval computation for depth 13, residue 6352. -/
theorem bounds_13_6352 : exactInterval 13 6352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6352 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6352) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6352 : oddCount 6352 13 = 2 ∧ acceleratedOrbit 13 6352 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6352 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6352) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6352.1, data_13_6352.2]

/-- Complete interval computation for depth 13, residue 6353. -/
theorem bounds_13_6353 : exactInterval 13 6353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6353 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6353) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6353 : oddCount 6353 13 = 8 ∧ acceleratedOrbit 13 6353 = 5093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6353 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6353) = 3 ^ 8 * m + 5093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6353.1, data_13_6353.2]

/-- Complete interval computation for depth 13, residue 6354. -/
theorem bounds_13_6354 : exactInterval 13 6354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6354 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6354) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6354 : oddCount 6354 13 = 8 ∧ acceleratedOrbit 13 6354 = 5093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6354 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6354) = 3 ^ 8 * m + 5093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6354.1, data_13_6354.2]

/-- Complete interval computation for depth 13, residue 6355. -/
theorem bounds_13_6355 : exactInterval 13 6355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6355 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6355) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6355 : oddCount 6355 13 = 8 ∧ acceleratedOrbit 13 6355 = 5093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6355 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6355) = 3 ^ 8 * m + 5093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6355.1, data_13_6355.2]

/-- Complete interval computation for depth 13, residue 6356. -/
theorem bounds_13_6356 : exactInterval 13 6356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6356 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6356) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6356 : oddCount 6356 13 = 2 ∧ acceleratedOrbit 13 6356 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6356 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6356) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6356.1, data_13_6356.2]

/-- Complete interval computation for depth 13, residue 6357. -/
theorem bounds_13_6357 : exactInterval 13 6357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6357 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6357) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6357 : oddCount 6357 13 = 2 ∧ acceleratedOrbit 13 6357 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6357 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6357) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6357.1, data_13_6357.2]

/-- Complete interval computation for depth 13, residue 6358. -/
theorem bounds_13_6358 : exactInterval 13 6358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6358 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6358) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6358 : oddCount 6358 13 = 8 ∧ acceleratedOrbit 13 6358 = 5096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6358 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6358) = 3 ^ 8 * m + 5096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6358.1, data_13_6358.2]

/-- Complete interval computation for depth 13, residue 6359. -/
theorem bounds_13_6359 : exactInterval 13 6359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6359 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6359) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6359 : oddCount 6359 13 = 8 ∧ acceleratedOrbit 13 6359 = 5096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6359 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6359) = 3 ^ 8 * m + 5096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6359.1, data_13_6359.2]

/-- Complete interval computation for depth 13, residue 6360. -/
theorem bounds_13_6360 : exactInterval 13 6360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6360 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6360) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6360 : oddCount 6360 13 = 9 ∧ acceleratedOrbit 13 6360 = 15308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6360 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6360) = 3 ^ 9 * m + 15308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6360.1, data_13_6360.2]

/-- Complete interval computation for depth 13, residue 6361. -/
theorem bounds_13_6361 : exactInterval 13 6361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6361 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6361) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6361 : oddCount 6361 13 = 8 ∧ acceleratedOrbit 13 6361 = 5102 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6361 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6361) = 3 ^ 8 * m + 5102 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6361.1, data_13_6361.2]

/-- Complete interval computation for depth 13, residue 6362. -/
theorem bounds_13_6362 : exactInterval 13 6362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6362 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6362) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6362 : oddCount 6362 13 = 9 ∧ acceleratedOrbit 13 6362 = 15308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6362 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6362) = 3 ^ 9 * m + 15308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6362.1, data_13_6362.2]

/-- Complete interval computation for depth 13, residue 6363. -/
theorem bounds_13_6363 : exactInterval 13 6363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6363 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6363) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6363 : oddCount 6363 13 = 8 ∧ acceleratedOrbit 13 6363 = 5098 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6363 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6363) = 3 ^ 8 * m + 5098 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6363.1, data_13_6363.2]

end Collatz.Research.StoppingAtlas.Batch0881
