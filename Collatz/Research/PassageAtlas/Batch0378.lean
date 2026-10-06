import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0378

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 12353. -/
theorem bounds_15_12353 : exactInterval 15 12353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12353 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12353) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12353 : oddCount 12353 15 = 6 ∧ acceleratedOrbit 15 12353 = 275 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12353 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12353) = 3 ^ 6 * m + 275 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12353.1, data_15_12353.2]

/-- Complete interval computation for depth 15, residue 12354. -/
theorem bounds_15_12354 : exactInterval 15 12354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12354 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12354) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12354 : oddCount 12354 15 = 6 ∧ acceleratedOrbit 15 12354 = 275 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12354 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12354) = 3 ^ 6 * m + 275 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12354.1, data_15_12354.2]

/-- Complete interval computation for depth 15, residue 12355. -/
theorem bounds_15_12355 : exactInterval 15 12355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12355 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12355) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12355 : oddCount 12355 15 = 6 ∧ acceleratedOrbit 15 12355 = 275 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12355 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12355) = 3 ^ 6 * m + 275 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12355.1, data_15_12355.2]

/-- Complete interval computation for depth 15, residue 12356. -/
theorem bounds_15_12356 : exactInterval 15 12356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12356 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12356) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12356 : oddCount 12356 15 = 5 ∧ acceleratedOrbit 15 12356 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12356 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12356) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12356.1, data_15_12356.2]

/-- Complete interval computation for depth 15, residue 12357. -/
theorem bounds_15_12357 : exactInterval 15 12357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12357 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12357) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12357 : oddCount 12357 15 = 5 ∧ acceleratedOrbit 15 12357 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12357 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12357) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12357.1, data_15_12357.2]

/-- Complete interval computation for depth 15, residue 12358. -/
theorem bounds_15_12358 : exactInterval 15 12358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12358 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12358) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12358 : oddCount 12358 15 = 5 ∧ acceleratedOrbit 15 12358 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12358 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12358) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12358.1, data_15_12358.2]

/-- Complete interval computation for depth 15, residue 12359. -/
theorem bounds_15_12359 : exactInterval 15 12359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12359 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12359) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12359 : oddCount 12359 15 = 12 ∧ acceleratedOrbit 15 12359 = 200474 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12359 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12359) = 3 ^ 12 * m + 200474 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12359.1, data_15_12359.2]

/-- Complete interval computation for depth 15, residue 12360. -/
theorem bounds_15_12360 : exactInterval 15 12360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12360 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12360) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12360 : oddCount 12360 15 = 7 ∧ acceleratedOrbit 15 12360 = 827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12360 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12360) = 3 ^ 7 * m + 827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12360.1, data_15_12360.2]

/-- Complete interval computation for depth 15, residue 12361. -/
theorem bounds_15_12361 : exactInterval 15 12361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12361 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12361) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12361 : oddCount 12361 15 = 9 ∧ acceleratedOrbit 15 12361 = 7427 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12361 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12361) = 3 ^ 9 * m + 7427 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12361.1, data_15_12361.2]

/-- Complete interval computation for depth 15, residue 12362. -/
theorem bounds_15_12362 : exactInterval 15 12362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12362 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12362) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12362 : oddCount 12362 15 = 7 ∧ acceleratedOrbit 15 12362 = 827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12362 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12362) = 3 ^ 7 * m + 827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12362.1, data_15_12362.2]

/-- Complete interval computation for depth 15, residue 12363. -/
theorem bounds_15_12363 : exactInterval 15 12363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12363 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12363) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12363 : oddCount 12363 15 = 5 ∧ acceleratedOrbit 15 12363 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12363 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12363) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12363.1, data_15_12363.2]

/-- Complete interval computation for depth 15, residue 12364. -/
theorem bounds_15_12364 : exactInterval 15 12364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12364 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12364) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12364 : oddCount 12364 15 = 7 ∧ acceleratedOrbit 15 12364 = 827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12364 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12364) = 3 ^ 7 * m + 827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12364.1, data_15_12364.2]

/-- Complete interval computation for depth 15, residue 12365. -/
theorem bounds_15_12365 : exactInterval 15 12365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12365 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12365) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12365 : oddCount 12365 15 = 7 ∧ acceleratedOrbit 15 12365 = 827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12365 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12365) = 3 ^ 7 * m + 827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12365.1, data_15_12365.2]

/-- Complete interval computation for depth 15, residue 12366. -/
theorem bounds_15_12366 : exactInterval 15 12366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12366 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12366) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12366 : oddCount 12366 15 = 8 ∧ acceleratedOrbit 15 12366 = 2477 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12366 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12366) = 3 ^ 8 * m + 2477 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12366.1, data_15_12366.2]

/-- Complete interval computation for depth 15, residue 12367. -/
theorem bounds_15_12367 : exactInterval 15 12367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12367 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12367) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12367 : oddCount 12367 15 = 8 ∧ acceleratedOrbit 15 12367 = 2477 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12367 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12367) = 3 ^ 8 * m + 2477 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12367.1, data_15_12367.2]

/-- Complete interval computation for depth 15, residue 12368. -/
theorem bounds_15_12368 : exactInterval 15 12368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12368 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12368) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12368 : oddCount 12368 15 = 4 ∧ acceleratedOrbit 15 12368 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12368 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12368) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12368.1, data_15_12368.2]

/-- Complete interval computation for depth 15, residue 12369. -/
theorem bounds_15_12369 : exactInterval 15 12369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12369 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12369) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12369 : oddCount 12369 15 = 7 ∧ acceleratedOrbit 15 12369 = 827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12369 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12369) = 3 ^ 7 * m + 827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12369.1, data_15_12369.2]

/-- Complete interval computation for depth 15, residue 12370. -/
theorem bounds_15_12370 : exactInterval 15 12370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12370 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12370) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12370 : oddCount 12370 15 = 9 ∧ acceleratedOrbit 15 12370 = 7433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12370 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12370) = 3 ^ 9 * m + 7433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12370.1, data_15_12370.2]

/-- Complete interval computation for depth 15, residue 12371. -/
theorem bounds_15_12371 : exactInterval 15 12371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12371 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12371) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12371 : oddCount 12371 15 = 9 ∧ acceleratedOrbit 15 12371 = 7433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12371 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12371) = 3 ^ 9 * m + 7433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12371.1, data_15_12371.2]

/-- Complete interval computation for depth 15, residue 12372. -/
theorem bounds_15_12372 : exactInterval 15 12372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12372 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12372) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12372 : oddCount 12372 15 = 4 ∧ acceleratedOrbit 15 12372 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12372 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12372) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12372.1, data_15_12372.2]

/-- Complete interval computation for depth 15, residue 12373. -/
theorem bounds_15_12373 : exactInterval 15 12373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12373 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12373) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12373 : oddCount 12373 15 = 4 ∧ acceleratedOrbit 15 12373 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12373 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12373) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12373.1, data_15_12373.2]

/-- Complete interval computation for depth 15, residue 12374. -/
theorem bounds_15_12374 : exactInterval 15 12374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12374 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12374) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12374 : oddCount 12374 15 = 7 ∧ acceleratedOrbit 15 12374 = 827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12374 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12374) = 3 ^ 7 * m + 827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12374.1, data_15_12374.2]

/-- Complete interval computation for depth 15, residue 12375. -/
theorem bounds_15_12375 : exactInterval 15 12375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12375 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12375) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12375 : oddCount 12375 15 = 7 ∧ acceleratedOrbit 15 12375 = 827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12375 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12375) = 3 ^ 7 * m + 827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12375.1, data_15_12375.2]

/-- Complete interval computation for depth 15, residue 12376. -/
theorem bounds_15_12376 : exactInterval 15 12376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12376 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12376) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12376 : oddCount 12376 15 = 5 ∧ acceleratedOrbit 15 12376 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12376 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12376) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12376.1, data_15_12376.2]

/-- Complete interval computation for depth 15, residue 12377. -/
theorem bounds_15_12377 : exactInterval 15 12377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12377 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12377) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12377 : oddCount 12377 15 = 7 ∧ acceleratedOrbit 15 12377 = 827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12377 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12377) = 3 ^ 7 * m + 827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12377.1, data_15_12377.2]

/-- Complete interval computation for depth 15, residue 12378. -/
theorem bounds_15_12378 : exactInterval 15 12378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12378 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12378) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12378 : oddCount 12378 15 = 5 ∧ acceleratedOrbit 15 12378 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12378 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12378) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12378.1, data_15_12378.2]

/-- Complete interval computation for depth 15, residue 12379. -/
theorem bounds_15_12379 : exactInterval 15 12379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12379 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12379) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12379 : oddCount 12379 15 = 11 ∧ acceleratedOrbit 15 12379 = 66932 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12379 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12379) = 3 ^ 11 * m + 66932 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12379.1, data_15_12379.2]

/-- Complete interval computation for depth 15, residue 12380. -/
theorem bounds_15_12380 : exactInterval 15 12380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12380 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12380) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12380 : oddCount 12380 15 = 5 ∧ acceleratedOrbit 15 12380 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12380 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12380) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12380.1, data_15_12380.2]

/-- Complete interval computation for depth 15, residue 12381. -/
theorem bounds_15_12381 : exactInterval 15 12381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12381 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12381) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12381 : oddCount 12381 15 = 5 ∧ acceleratedOrbit 15 12381 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12381 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12381) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12381.1, data_15_12381.2]

/-- Complete interval computation for depth 15, residue 12382. -/
theorem bounds_15_12382 : exactInterval 15 12382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12382 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12382) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12382 : oddCount 12382 15 = 10 ∧ acceleratedOrbit 15 12382 = 22319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12382 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12382) = 3 ^ 10 * m + 22319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12382.1, data_15_12382.2]

/-- Complete interval computation for depth 15, residue 12383. -/
theorem bounds_15_12383 : exactInterval 15 12383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12383 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12383) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12383 : oddCount 12383 15 = 10 ∧ acceleratedOrbit 15 12383 = 22319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12383 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12383) = 3 ^ 10 * m + 22319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12383.1, data_15_12383.2]

/-- Complete interval computation for depth 15, residue 12384. -/
theorem bounds_15_12384 : exactInterval 15 12384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12384 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12384) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12384 : oddCount 12384 15 = 4 ∧ acceleratedOrbit 15 12384 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12384 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12384) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12384.1, data_15_12384.2]

/-- Complete interval computation for depth 15, residue 12385. -/
theorem bounds_15_12385 : exactInterval 15 12385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12385 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12385) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12385 : oddCount 12385 15 = 9 ∧ acceleratedOrbit 15 12385 = 7442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12385 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12385) = 3 ^ 9 * m + 7442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12385.1, data_15_12385.2]

end Collatz.Research.PassageAtlas.Batch0378
