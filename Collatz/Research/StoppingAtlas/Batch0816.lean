import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0816

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5350. -/
theorem bounds_13_5350 : exactInterval 13 5350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5350 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5350) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5350 : oddCount 5350 13 = 8 ∧ acceleratedOrbit 13 5350 = 4292 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5350 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5350) = 3 ^ 8 * m + 4292 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5350.1, data_13_5350.2]

/-- Complete interval computation for depth 13, residue 5351. -/
theorem bounds_13_5351 : exactInterval 13 5351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5351 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5351) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5351 : oddCount 5351 13 = 10 ∧ acceleratedOrbit 13 5351 = 38582 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5351 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5351) = 3 ^ 10 * m + 38582 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5351.1, data_13_5351.2]

/-- Complete interval computation for depth 13, residue 5352. -/
theorem bounds_13_5352 : exactInterval 13 5352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5352 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5352) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5352 : oddCount 5352 13 = 6 ∧ acceleratedOrbit 13 5352 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5352 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5352) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5352.1, data_13_5352.2]

/-- Complete interval computation for depth 13, residue 5353. -/
theorem bounds_13_5353 : exactInterval 13 5353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5353 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5353) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5353 : oddCount 5353 13 = 7 ∧ acceleratedOrbit 13 5353 = 1430 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5353 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5353) = 3 ^ 7 * m + 1430 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5353.1, data_13_5353.2]

/-- Complete interval computation for depth 13, residue 5354. -/
theorem bounds_13_5354 : exactInterval 13 5354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5354 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5354) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5354 : oddCount 5354 13 = 6 ∧ acceleratedOrbit 13 5354 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5354 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5354) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5354.1, data_13_5354.2]

/-- Complete interval computation for depth 13, residue 5355. -/
theorem bounds_13_5355 : exactInterval 13 5355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5355 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5355) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5355 : oddCount 5355 13 = 9 ∧ acceleratedOrbit 13 5355 = 12872 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5355 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5355) = 3 ^ 9 * m + 12872 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5355.1, data_13_5355.2]

/-- Complete interval computation for depth 13, residue 5356. -/
theorem bounds_13_5356 : exactInterval 13 5356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5356 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5356) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5356 : oddCount 5356 13 = 4 ∧ acceleratedOrbit 13 5356 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5356 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5356) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5356.1, data_13_5356.2]

/-- Complete interval computation for depth 13, residue 5357. -/
theorem bounds_13_5357 : exactInterval 13 5357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5357 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5357) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5357 : oddCount 5357 13 = 4 ∧ acceleratedOrbit 13 5357 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5357 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5357) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5357.1, data_13_5357.2]

/-- Complete interval computation for depth 13, residue 5358. -/
theorem bounds_13_5358 : exactInterval 13 5358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5358 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5358) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5358 : oddCount 5358 13 = 4 ∧ acceleratedOrbit 13 5358 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5358 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5358) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5358.1, data_13_5358.2]

/-- Complete interval computation for depth 13, residue 5359. -/
theorem bounds_13_5359 : exactInterval 13 5359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5359 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5359) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5359 : oddCount 5359 13 = 12 ∧ acceleratedOrbit 13 5359 = 347732 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5359 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5359) = 3 ^ 12 * m + 347732 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5359.1, data_13_5359.2]

/-- Complete interval computation for depth 13, residue 5360. -/
theorem bounds_13_5360 : exactInterval 13 5360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5360 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5360) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5360 : oddCount 5360 13 = 6 ∧ acceleratedOrbit 13 5360 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5360 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5360) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5360.1, data_13_5360.2]

/-- Complete interval computation for depth 13, residue 5361. -/
theorem bounds_13_5361 : exactInterval 13 5361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5361 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5361) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5361 : oddCount 5361 13 = 6 ∧ acceleratedOrbit 13 5361 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5361 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5361) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5361.1, data_13_5361.2]

/-- Complete interval computation for depth 13, residue 5362. -/
theorem bounds_13_5362 : exactInterval 13 5362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5362 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5362) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5362 : oddCount 5362 13 = 7 ∧ acceleratedOrbit 13 5362 = 1433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5362 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5362) = 3 ^ 7 * m + 1433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5362.1, data_13_5362.2]

/-- Complete interval computation for depth 13, residue 5363. -/
theorem bounds_13_5363 : exactInterval 13 5363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5363 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5363) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5363 : oddCount 5363 13 = 7 ∧ acceleratedOrbit 13 5363 = 1433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5363 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5363) = 3 ^ 7 * m + 1433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5363.1, data_13_5363.2]

/-- Complete interval computation for depth 13, residue 5364. -/
theorem bounds_13_5364 : exactInterval 13 5364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5364 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5364) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5364 : oddCount 5364 13 = 6 ∧ acceleratedOrbit 13 5364 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5364 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5364) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5364.1, data_13_5364.2]

end Collatz.Research.StoppingAtlas.Batch0816
