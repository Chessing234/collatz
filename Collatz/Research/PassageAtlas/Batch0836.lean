import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0836

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 27361. -/
theorem bounds_15_27361 : exactInterval 15 27361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27361 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27361) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27361 : oddCount 27361 15 = 11 ∧ acceleratedOrbit 15 27361 = 147932 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27361 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27361) = 3 ^ 11 * m + 147932 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27361.1, data_15_27361.2]

/-- Complete interval computation for depth 15, residue 27362. -/
theorem bounds_15_27362 : exactInterval 15 27362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27362 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27362) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27362 : oddCount 27362 15 = 6 ∧ acceleratedOrbit 15 27362 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27362 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27362) = 3 ^ 6 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27362.1, data_15_27362.2]

/-- Complete interval computation for depth 15, residue 27363. -/
theorem bounds_15_27363 : exactInterval 15 27363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27363 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27363) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27363 : oddCount 27363 15 = 6 ∧ acceleratedOrbit 15 27363 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27363 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27363) = 3 ^ 6 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27363.1, data_15_27363.2]

/-- Complete interval computation for depth 15, residue 27364. -/
theorem bounds_15_27364 : exactInterval 15 27364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27364 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27364) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27364 : oddCount 27364 15 = 5 ∧ acceleratedOrbit 15 27364 = 203 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27364 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27364) = 3 ^ 5 * m + 203 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27364.1, data_15_27364.2]

/-- Complete interval computation for depth 15, residue 27365. -/
theorem bounds_15_27365 : exactInterval 15 27365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27365 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27365) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27365 : oddCount 27365 15 = 5 ∧ acceleratedOrbit 15 27365 = 203 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27365 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27365) = 3 ^ 5 * m + 203 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27365.1, data_15_27365.2]

/-- Complete interval computation for depth 15, residue 27366. -/
theorem bounds_15_27366 : exactInterval 15 27366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27366 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27366) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27366 : oddCount 27366 15 = 5 ∧ acceleratedOrbit 15 27366 = 203 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27366 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27366) = 3 ^ 5 * m + 203 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27366.1, data_15_27366.2]

/-- Complete interval computation for depth 15, residue 27367. -/
theorem bounds_15_27367 : exactInterval 15 27367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27367 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27367) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27367 : oddCount 27367 15 = 12 ∧ acceleratedOrbit 15 27367 = 443870 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27367 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27367) = 3 ^ 12 * m + 443870 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27367.1, data_15_27367.2]

/-- Complete interval computation for depth 15, residue 27368. -/
theorem bounds_15_27368 : exactInterval 15 27368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27368 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27368) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27368 : oddCount 27368 15 = 6 ∧ acceleratedOrbit 15 27368 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27368 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27368) = 3 ^ 6 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27368.1, data_15_27368.2]

/-- Complete interval computation for depth 15, residue 27369. -/
theorem bounds_15_27369 : exactInterval 15 27369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27369 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27369) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27369 : oddCount 27369 15 = 10 ∧ acceleratedOrbit 15 27369 = 49324 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27369 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27369) = 3 ^ 10 * m + 49324 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27369.1, data_15_27369.2]

/-- Complete interval computation for depth 15, residue 27370. -/
theorem bounds_15_27370 : exactInterval 15 27370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27370 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27370) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27370 : oddCount 27370 15 = 6 ∧ acceleratedOrbit 15 27370 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27370 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27370) = 3 ^ 6 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27370.1, data_15_27370.2]

/-- Complete interval computation for depth 15, residue 27371. -/
theorem bounds_15_27371 : exactInterval 15 27371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27371 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27371) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27371 : oddCount 27371 15 = 11 ∧ acceleratedOrbit 15 27371 = 147986 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27371 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27371) = 3 ^ 11 * m + 147986 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27371.1, data_15_27371.2]

/-- Complete interval computation for depth 15, residue 27372. -/
theorem bounds_15_27372 : exactInterval 15 27372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27372 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27372) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27372 : oddCount 27372 15 = 8 ∧ acceleratedOrbit 15 27372 = 5483 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27372 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27372) = 3 ^ 8 * m + 5483 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27372.1, data_15_27372.2]

/-- Complete interval computation for depth 15, residue 27373. -/
theorem bounds_15_27373 : exactInterval 15 27373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27373 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27373) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27373 : oddCount 27373 15 = 8 ∧ acceleratedOrbit 15 27373 = 5483 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27373 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27373) = 3 ^ 8 * m + 5483 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27373.1, data_15_27373.2]

/-- Complete interval computation for depth 15, residue 27374. -/
theorem bounds_15_27374 : exactInterval 15 27374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27374 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27374) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27374 : oddCount 27374 15 = 8 ∧ acceleratedOrbit 15 27374 = 5483 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27374 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27374) = 3 ^ 8 * m + 5483 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27374.1, data_15_27374.2]

/-- Complete interval computation for depth 15, residue 27375. -/
theorem bounds_15_27375 : exactInterval 15 27375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27375 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27375) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27375 : oddCount 27375 15 = 10 ∧ acceleratedOrbit 15 27375 = 49333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27375 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27375) = 3 ^ 10 * m + 49333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27375.1, data_15_27375.2]

/-- Complete interval computation for depth 15, residue 27376. -/
theorem bounds_15_27376 : exactInterval 15 27376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27376 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27376) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27376 : oddCount 27376 15 = 7 ∧ acceleratedOrbit 15 27376 = 1829 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27376 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27376) = 3 ^ 7 * m + 1829 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27376.1, data_15_27376.2]

/-- Complete interval computation for depth 15, residue 27377. -/
theorem bounds_15_27377 : exactInterval 15 27377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27377 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27377) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27377 : oddCount 27377 15 = 6 ∧ acceleratedOrbit 15 27377 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27377 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27377) = 3 ^ 6 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27377.1, data_15_27377.2]

/-- Complete interval computation for depth 15, residue 27378. -/
theorem bounds_15_27378 : exactInterval 15 27378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27378 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27378) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27378 : oddCount 27378 15 = 9 ∧ acceleratedOrbit 15 27378 = 16448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27378 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27378) = 3 ^ 9 * m + 16448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27378.1, data_15_27378.2]

/-- Complete interval computation for depth 15, residue 27379. -/
theorem bounds_15_27379 : exactInterval 15 27379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27379 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27379) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27379 : oddCount 27379 15 = 9 ∧ acceleratedOrbit 15 27379 = 16448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27379 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27379) = 3 ^ 9 * m + 16448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27379.1, data_15_27379.2]

/-- Complete interval computation for depth 15, residue 27380. -/
theorem bounds_15_27380 : exactInterval 15 27380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27380 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27380) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27380 : oddCount 27380 15 = 7 ∧ acceleratedOrbit 15 27380 = 1829 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27380 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27380) = 3 ^ 7 * m + 1829 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27380.1, data_15_27380.2]

/-- Complete interval computation for depth 15, residue 27381. -/
theorem bounds_15_27381 : exactInterval 15 27381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27381 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27381) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27381 : oddCount 27381 15 = 7 ∧ acceleratedOrbit 15 27381 = 1829 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27381 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27381) = 3 ^ 7 * m + 1829 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27381.1, data_15_27381.2]

/-- Complete interval computation for depth 15, residue 27382. -/
theorem bounds_15_27382 : exactInterval 15 27382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27382 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27382) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27382 : oddCount 27382 15 = 7 ∧ acceleratedOrbit 15 27382 = 1828 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27382 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27382) = 3 ^ 7 * m + 1828 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27382.1, data_15_27382.2]

/-- Complete interval computation for depth 15, residue 27383. -/
theorem bounds_15_27383 : exactInterval 15 27383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27383 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27383) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27383 : oddCount 27383 15 = 7 ∧ acceleratedOrbit 15 27383 = 1828 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27383 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27383) = 3 ^ 7 * m + 1828 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27383.1, data_15_27383.2]

/-- Complete interval computation for depth 15, residue 27384. -/
theorem bounds_15_27384 : exactInterval 15 27384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27384 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27384) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27384 : oddCount 27384 15 = 7 ∧ acceleratedOrbit 15 27384 = 1829 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27384 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27384) = 3 ^ 7 * m + 1829 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27384.1, data_15_27384.2]

/-- Complete interval computation for depth 15, residue 27385. -/
theorem bounds_15_27385 : exactInterval 15 27385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27385 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27385) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27385 : oddCount 27385 15 = 7 ∧ acceleratedOrbit 15 27385 = 1828 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27385 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27385) = 3 ^ 7 * m + 1828 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27385.1, data_15_27385.2]

/-- Complete interval computation for depth 15, residue 27386. -/
theorem bounds_15_27386 : exactInterval 15 27386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27386 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27386) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27386 : oddCount 27386 15 = 7 ∧ acceleratedOrbit 15 27386 = 1829 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27386 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27386) = 3 ^ 7 * m + 1829 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27386.1, data_15_27386.2]

/-- Complete interval computation for depth 15, residue 27387. -/
theorem bounds_15_27387 : exactInterval 15 27387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27387 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27387) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27387 : oddCount 27387 15 = 12 ∧ acceleratedOrbit 15 27387 = 444203 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27387 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27387) = 3 ^ 12 * m + 444203 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27387.1, data_15_27387.2]

/-- Complete interval computation for depth 15, residue 27388. -/
theorem bounds_15_27388 : exactInterval 15 27388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27388 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27388) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27388 : oddCount 27388 15 = 9 ∧ acceleratedOrbit 15 27388 = 16454 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27388 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27388) = 3 ^ 9 * m + 16454 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27388.1, data_15_27388.2]

/-- Complete interval computation for depth 15, residue 27389. -/
theorem bounds_15_27389 : exactInterval 15 27389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27389 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27389) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27389 : oddCount 27389 15 = 9 ∧ acceleratedOrbit 15 27389 = 16454 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27389 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27389) = 3 ^ 9 * m + 16454 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27389.1, data_15_27389.2]

/-- Complete interval computation for depth 15, residue 27390. -/
theorem bounds_15_27390 : exactInterval 15 27390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27390 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27390) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27390 : oddCount 27390 15 = 9 ∧ acceleratedOrbit 15 27390 = 16454 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27390 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27390) = 3 ^ 9 * m + 16454 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27390.1, data_15_27390.2]

/-- Complete interval computation for depth 15, residue 27391. -/
theorem bounds_15_27391 : exactInterval 15 27391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27391 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27391) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27391 : oddCount 27391 15 = 11 ∧ acceleratedOrbit 15 27391 = 148085 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27391 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27391) = 3 ^ 11 * m + 148085 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27391.1, data_15_27391.2]

/-- Complete interval computation for depth 15, residue 27392. -/
theorem bounds_15_27392 : exactInterval 15 27392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27392 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27392) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27392 : oddCount 27392 15 = 5 ∧ acceleratedOrbit 15 27392 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27392 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27392) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27392.1, data_15_27392.2]

/-- Complete interval computation for depth 15, residue 27393. -/
theorem bounds_15_27393 : exactInterval 15 27393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27393 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27393) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27393 : oddCount 27393 15 = 7 ∧ acceleratedOrbit 15 27393 = 1829 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27393 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27393) = 3 ^ 7 * m + 1829 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27393.1, data_15_27393.2]

end Collatz.Research.PassageAtlas.Batch0836
