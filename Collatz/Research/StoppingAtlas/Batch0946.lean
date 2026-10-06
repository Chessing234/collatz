import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0946

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7347. -/
theorem bounds_13_7347 : exactInterval 13 7347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7347 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7347) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7347 : oddCount 7347 13 = 7 ∧ acceleratedOrbit 13 7347 = 1964 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7347 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7347) = 3 ^ 7 * m + 1964 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7347.1, data_13_7347.2]

/-- Complete interval computation for depth 13, residue 7348. -/
theorem bounds_13_7348 : exactInterval 13 7348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7348 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7348) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7348 : oddCount 7348 13 = 4 ∧ acceleratedOrbit 13 7348 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7348 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7348) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7348.1, data_13_7348.2]

/-- Complete interval computation for depth 13, residue 7349. -/
theorem bounds_13_7349 : exactInterval 13 7349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7349 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7349) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7349 : oddCount 7349 13 = 4 ∧ acceleratedOrbit 13 7349 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7349 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7349) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7349.1, data_13_7349.2]

/-- Complete interval computation for depth 13, residue 7350. -/
theorem bounds_13_7350 : exactInterval 13 7350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7350 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7350) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7350 : oddCount 7350 13 = 7 ∧ acceleratedOrbit 13 7350 = 1963 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7350 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7350) = 3 ^ 7 * m + 1963 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7350.1, data_13_7350.2]

/-- Complete interval computation for depth 13, residue 7351. -/
theorem bounds_13_7351 : exactInterval 13 7351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7351 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7351) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7351 : oddCount 7351 13 = 7 ∧ acceleratedOrbit 13 7351 = 1963 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7351 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7351) = 3 ^ 7 * m + 1963 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7351.1, data_13_7351.2]

/-- Complete interval computation for depth 13, residue 7352. -/
theorem bounds_13_7352 : exactInterval 13 7352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7352 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7352) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7352 : oddCount 7352 13 = 4 ∧ acceleratedOrbit 13 7352 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7352 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7352) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7352.1, data_13_7352.2]

/-- Complete interval computation for depth 13, residue 7353. -/
theorem bounds_13_7353 : exactInterval 13 7353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7353 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7353) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7353 : oddCount 7353 13 = 7 ∧ acceleratedOrbit 13 7353 = 1964 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7353 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7353) = 3 ^ 7 * m + 1964 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7353.1, data_13_7353.2]

/-- Complete interval computation for depth 13, residue 7354. -/
theorem bounds_13_7354 : exactInterval 13 7354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7354 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7354) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7354 : oddCount 7354 13 = 4 ∧ acceleratedOrbit 13 7354 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7354 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7354) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7354.1, data_13_7354.2]

/-- Complete interval computation for depth 13, residue 7355. -/
theorem bounds_13_7355 : exactInterval 13 7355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7355 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7355) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7355 : oddCount 7355 13 = 9 ∧ acceleratedOrbit 13 7355 = 17678 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7355 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7355) = 3 ^ 9 * m + 17678 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7355.1, data_13_7355.2]

/-- Complete interval computation for depth 13, residue 7356. -/
theorem bounds_13_7356 : exactInterval 13 7356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7356 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7356) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7356 : oddCount 7356 13 = 6 ∧ acceleratedOrbit 13 7356 = 655 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7356 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7356) = 3 ^ 6 * m + 655 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7356.1, data_13_7356.2]

/-- Complete interval computation for depth 13, residue 7357. -/
theorem bounds_13_7357 : exactInterval 13 7357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7357 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7357) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7357 : oddCount 7357 13 = 6 ∧ acceleratedOrbit 13 7357 = 655 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7357 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7357) = 3 ^ 6 * m + 655 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7357.1, data_13_7357.2]

/-- Complete interval computation for depth 13, residue 7358. -/
theorem bounds_13_7358 : exactInterval 13 7358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7358 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7358) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7358 : oddCount 7358 13 = 6 ∧ acceleratedOrbit 13 7358 = 655 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7358 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7358) = 3 ^ 6 * m + 655 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7358.1, data_13_7358.2]

/-- Complete interval computation for depth 13, residue 7359. -/
theorem bounds_13_7359 : exactInterval 13 7359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7359 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7359) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7359 : oddCount 7359 13 = 10 ∧ acceleratedOrbit 13 7359 = 53054 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7359 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7359) = 3 ^ 10 * m + 53054 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7359.1, data_13_7359.2]

/-- Complete interval computation for depth 13, residue 7360. -/
theorem bounds_13_7360 : exactInterval 13 7360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7360 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7360) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7360 : oddCount 7360 13 = 4 ∧ acceleratedOrbit 13 7360 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7360 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7360) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7360.1, data_13_7360.2]

/-- Complete interval computation for depth 13, residue 7361. -/
theorem bounds_13_7361 : exactInterval 13 7361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7361 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7361) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7361 : oddCount 7361 13 = 6 ∧ acceleratedOrbit 13 7361 = 656 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7361 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7361) = 3 ^ 6 * m + 656 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7361.1, data_13_7361.2]

end Collatz.Research.StoppingAtlas.Batch0946
