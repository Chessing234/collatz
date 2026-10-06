import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0751

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4352. -/
theorem bounds_13_4352 : exactInterval 13 4352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4352 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4352) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4352 : oddCount 4352 13 = 2 ∧ acceleratedOrbit 13 4352 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4352 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4352) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4352.1, data_13_4352.2]

/-- Complete interval computation for depth 13, residue 4353. -/
theorem bounds_13_4353 : exactInterval 13 4353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4353 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4353) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4353 : oddCount 4353 13 = 6 ∧ acceleratedOrbit 13 4353 = 388 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4353 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4353) = 3 ^ 6 * m + 388 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4353.1, data_13_4353.2]

/-- Complete interval computation for depth 13, residue 4354. -/
theorem bounds_13_4354 : exactInterval 13 4354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4354 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4354) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4354 : oddCount 4354 13 = 6 ∧ acceleratedOrbit 13 4354 = 388 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4354 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4354) = 3 ^ 6 * m + 388 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4354.1, data_13_4354.2]

/-- Complete interval computation for depth 13, residue 4355. -/
theorem bounds_13_4355 : exactInterval 13 4355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4355 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4355) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4355 : oddCount 4355 13 = 6 ∧ acceleratedOrbit 13 4355 = 388 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4355 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4355) = 3 ^ 6 * m + 388 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4355.1, data_13_4355.2]

/-- Complete interval computation for depth 13, residue 4356. -/
theorem bounds_13_4356 : exactInterval 13 4356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4356 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4356) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4356 : oddCount 4356 13 = 5 ∧ acceleratedOrbit 13 4356 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4356 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4356) = 3 ^ 5 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4356.1, data_13_4356.2]

/-- Complete interval computation for depth 13, residue 4357. -/
theorem bounds_13_4357 : exactInterval 13 4357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4357 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4357) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4357 : oddCount 4357 13 = 5 ∧ acceleratedOrbit 13 4357 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4357 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4357) = 3 ^ 5 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4357.1, data_13_4357.2]

/-- Complete interval computation for depth 13, residue 4358. -/
theorem bounds_13_4358 : exactInterval 13 4358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4358 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4358) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4358 : oddCount 4358 13 = 5 ∧ acceleratedOrbit 13 4358 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4358 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4358) = 3 ^ 5 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4358.1, data_13_4358.2]

/-- Complete interval computation for depth 13, residue 4359. -/
theorem bounds_13_4359 : exactInterval 13 4359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4359 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4359) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4359 : oddCount 4359 13 = 8 ∧ acceleratedOrbit 13 4359 = 3493 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4359 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4359) = 3 ^ 8 * m + 3493 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4359.1, data_13_4359.2]

/-- Complete interval computation for depth 13, residue 4360. -/
theorem bounds_13_4360 : exactInterval 13 4360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4360 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4360) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4360 : oddCount 4360 13 = 5 ∧ acceleratedOrbit 13 4360 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4360 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4360) = 3 ^ 5 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4360.1, data_13_4360.2]

/-- Complete interval computation for depth 13, residue 4361. -/
theorem bounds_13_4361 : exactInterval 13 4361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4361 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4361) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4361 : oddCount 4361 13 = 7 ∧ acceleratedOrbit 13 4361 = 1165 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4361 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4361) = 3 ^ 7 * m + 1165 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4361.1, data_13_4361.2]

/-- Complete interval computation for depth 13, residue 4362. -/
theorem bounds_13_4362 : exactInterval 13 4362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4362 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4362) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4362 : oddCount 4362 13 = 5 ∧ acceleratedOrbit 13 4362 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4362 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4362) = 3 ^ 5 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4362.1, data_13_4362.2]

/-- Complete interval computation for depth 13, residue 4363. -/
theorem bounds_13_4363 : exactInterval 13 4363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4363 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4363) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4363 : oddCount 4363 13 = 6 ∧ acceleratedOrbit 13 4363 = 389 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4363 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4363) = 3 ^ 6 * m + 389 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4363.1, data_13_4363.2]

/-- Complete interval computation for depth 13, residue 4364. -/
theorem bounds_13_4364 : exactInterval 13 4364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4364 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4364) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4364 : oddCount 4364 13 = 5 ∧ acceleratedOrbit 13 4364 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4364 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4364) = 3 ^ 5 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4364.1, data_13_4364.2]

/-- Complete interval computation for depth 13, residue 4365. -/
theorem bounds_13_4365 : exactInterval 13 4365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4365 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4365) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4365 : oddCount 4365 13 = 5 ∧ acceleratedOrbit 13 4365 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4365 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4365) = 3 ^ 5 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4365.1, data_13_4365.2]

/-- Complete interval computation for depth 13, residue 4366. -/
theorem bounds_13_4366 : exactInterval 13 4366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4366 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4366) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4366 : oddCount 4366 13 = 6 ∧ acceleratedOrbit 13 4366 = 389 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4366 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4366) = 3 ^ 6 * m + 389 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4366.1, data_13_4366.2]

end Collatz.Research.StoppingAtlas.Batch0751
