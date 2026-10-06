import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0714

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 23363. -/
theorem bounds_15_23363 : exactInterval 15 23363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23363 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23363) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23363 : oddCount 23363 15 = 9 ∧ acceleratedOrbit 15 23363 = 14039 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23363 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23363) = 3 ^ 9 * m + 14039 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23363.1, data_15_23363.2]

/-- Complete interval computation for depth 15, residue 23364. -/
theorem bounds_15_23364 : exactInterval 15 23364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23364 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23364) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23364 : oddCount 23364 15 = 7 ∧ acceleratedOrbit 15 23364 = 1561 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23364 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23364) = 3 ^ 7 * m + 1561 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23364.1, data_15_23364.2]

/-- Complete interval computation for depth 15, residue 23365. -/
theorem bounds_15_23365 : exactInterval 15 23365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23365 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23365) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23365 : oddCount 23365 15 = 7 ∧ acceleratedOrbit 15 23365 = 1561 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23365 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23365) = 3 ^ 7 * m + 1561 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23365.1, data_15_23365.2]

/-- Complete interval computation for depth 15, residue 23366. -/
theorem bounds_15_23366 : exactInterval 15 23366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23366 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23366) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23366 : oddCount 23366 15 = 7 ∧ acceleratedOrbit 15 23366 = 1561 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23366 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23366) = 3 ^ 7 * m + 1561 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23366.1, data_15_23366.2]

/-- Complete interval computation for depth 15, residue 23367. -/
theorem bounds_15_23367 : exactInterval 15 23367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23367 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23367) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23367 : oddCount 23367 15 = 8 ∧ acceleratedOrbit 15 23367 = 4679 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23367 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23367) = 3 ^ 8 * m + 4679 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23367.1, data_15_23367.2]

/-- Complete interval computation for depth 15, residue 23368. -/
theorem bounds_15_23368 : exactInterval 15 23368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23368 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23368) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23368 : oddCount 23368 15 = 7 ∧ acceleratedOrbit 15 23368 = 1561 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23368 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23368) = 3 ^ 7 * m + 1561 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23368.1, data_15_23368.2]

/-- Complete interval computation for depth 15, residue 23369. -/
theorem bounds_15_23369 : exactInterval 15 23369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23369 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23369) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23369 : oddCount 23369 15 = 6 ∧ acceleratedOrbit 15 23369 = 520 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23369 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23369) = 3 ^ 6 * m + 520 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23369.1, data_15_23369.2]

/-- Complete interval computation for depth 15, residue 23370. -/
theorem bounds_15_23370 : exactInterval 15 23370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23370 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23370) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23370 : oddCount 23370 15 = 7 ∧ acceleratedOrbit 15 23370 = 1561 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23370 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23370) = 3 ^ 7 * m + 1561 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23370.1, data_15_23370.2]

/-- Complete interval computation for depth 15, residue 23371. -/
theorem bounds_15_23371 : exactInterval 15 23371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23371 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23371) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23371 : oddCount 23371 15 = 7 ∧ acceleratedOrbit 15 23371 = 1561 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23371 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23371) = 3 ^ 7 * m + 1561 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23371.1, data_15_23371.2]

/-- Complete interval computation for depth 15, residue 23372. -/
theorem bounds_15_23372 : exactInterval 15 23372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23372 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23372) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23372 : oddCount 23372 15 = 7 ∧ acceleratedOrbit 15 23372 = 1561 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23372 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23372) = 3 ^ 7 * m + 1561 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23372.1, data_15_23372.2]

/-- Complete interval computation for depth 15, residue 23373. -/
theorem bounds_15_23373 : exactInterval 15 23373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23373 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23373) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23373 : oddCount 23373 15 = 7 ∧ acceleratedOrbit 15 23373 = 1561 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23373 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23373) = 3 ^ 7 * m + 1561 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23373.1, data_15_23373.2]

/-- Complete interval computation for depth 15, residue 23374. -/
theorem bounds_15_23374 : exactInterval 15 23374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23374 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23374) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23374 : oddCount 23374 15 = 8 ∧ acceleratedOrbit 15 23374 = 4681 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23374 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23374) = 3 ^ 8 * m + 4681 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23374.1, data_15_23374.2]

/-- Complete interval computation for depth 15, residue 23375. -/
theorem bounds_15_23375 : exactInterval 15 23375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23375 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23375) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23375 : oddCount 23375 15 = 8 ∧ acceleratedOrbit 15 23375 = 4681 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23375 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23375) = 3 ^ 8 * m + 4681 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23375.1, data_15_23375.2]

/-- Complete interval computation for depth 15, residue 23376. -/
theorem bounds_15_23376 : exactInterval 15 23376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23376 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23376) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23376 : oddCount 23376 15 = 5 ∧ acceleratedOrbit 15 23376 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23376 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23376) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23376.1, data_15_23376.2]

/-- Complete interval computation for depth 15, residue 23377. -/
theorem bounds_15_23377 : exactInterval 15 23377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23377 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23377) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23377 : oddCount 23377 15 = 8 ∧ acceleratedOrbit 15 23377 = 4682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23377 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23377) = 3 ^ 8 * m + 4682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23377.1, data_15_23377.2]

/-- Complete interval computation for depth 15, residue 23378. -/
theorem bounds_15_23378 : exactInterval 15 23378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23378 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23378) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23378 : oddCount 23378 15 = 8 ∧ acceleratedOrbit 15 23378 = 4682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23378 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23378) = 3 ^ 8 * m + 4682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23378.1, data_15_23378.2]

/-- Complete interval computation for depth 15, residue 23379. -/
theorem bounds_15_23379 : exactInterval 15 23379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23379 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23379) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23379 : oddCount 23379 15 = 8 ∧ acceleratedOrbit 15 23379 = 4682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23379 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23379) = 3 ^ 8 * m + 4682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23379.1, data_15_23379.2]

/-- Complete interval computation for depth 15, residue 23380. -/
theorem bounds_15_23380 : exactInterval 15 23380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23380 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23380) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23380 : oddCount 23380 15 = 5 ∧ acceleratedOrbit 15 23380 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23380 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23380) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23380.1, data_15_23380.2]

/-- Complete interval computation for depth 15, residue 23381. -/
theorem bounds_15_23381 : exactInterval 15 23381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23381 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23381) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23381 : oddCount 23381 15 = 5 ∧ acceleratedOrbit 15 23381 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23381 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23381) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23381.1, data_15_23381.2]

/-- Complete interval computation for depth 15, residue 23382. -/
theorem bounds_15_23382 : exactInterval 15 23382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23382 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23382) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23382 : oddCount 23382 15 = 10 ∧ acceleratedOrbit 15 23382 = 42146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23382 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23382) = 3 ^ 10 * m + 42146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23382.1, data_15_23382.2]

/-- Complete interval computation for depth 15, residue 23383. -/
theorem bounds_15_23383 : exactInterval 15 23383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23383 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23383) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23383 : oddCount 23383 15 = 10 ∧ acceleratedOrbit 15 23383 = 42146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23383 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23383) = 3 ^ 10 * m + 42146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23383.1, data_15_23383.2]

/-- Complete interval computation for depth 15, residue 23384. -/
theorem bounds_15_23384 : exactInterval 15 23384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23384 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23384) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23384 : oddCount 23384 15 = 6 ∧ acceleratedOrbit 15 23384 = 521 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23384 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23384) = 3 ^ 6 * m + 521 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23384.1, data_15_23384.2]

/-- Complete interval computation for depth 15, residue 23385. -/
theorem bounds_15_23385 : exactInterval 15 23385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23385 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23385) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23385 : oddCount 23385 15 = 6 ∧ acceleratedOrbit 15 23385 = 521 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23385 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23385) = 3 ^ 6 * m + 521 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23385.1, data_15_23385.2]

/-- Complete interval computation for depth 15, residue 23386. -/
theorem bounds_15_23386 : exactInterval 15 23386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23386 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23386) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23386 : oddCount 23386 15 = 6 ∧ acceleratedOrbit 15 23386 = 521 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23386 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23386) = 3 ^ 6 * m + 521 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23386.1, data_15_23386.2]

/-- Complete interval computation for depth 15, residue 23387. -/
theorem bounds_15_23387 : exactInterval 15 23387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23387 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23387) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23387 : oddCount 23387 15 = 7 ∧ acceleratedOrbit 15 23387 = 1561 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23387 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23387) = 3 ^ 7 * m + 1561 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23387.1, data_15_23387.2]

/-- Complete interval computation for depth 15, residue 23388. -/
theorem bounds_15_23388 : exactInterval 15 23388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23388 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23388) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23388 : oddCount 23388 15 = 6 ∧ acceleratedOrbit 15 23388 = 521 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23388 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23388) = 3 ^ 6 * m + 521 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23388.1, data_15_23388.2]

/-- Complete interval computation for depth 15, residue 23389. -/
theorem bounds_15_23389 : exactInterval 15 23389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23389 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23389) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23389 : oddCount 23389 15 = 6 ∧ acceleratedOrbit 15 23389 = 521 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23389 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23389) = 3 ^ 6 * m + 521 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23389.1, data_15_23389.2]

/-- Complete interval computation for depth 15, residue 23390. -/
theorem bounds_15_23390 : exactInterval 15 23390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23390 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23390) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23390 : oddCount 23390 15 = 9 ∧ acceleratedOrbit 15 23390 = 14053 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23390 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23390) = 3 ^ 9 * m + 14053 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23390.1, data_15_23390.2]

/-- Complete interval computation for depth 15, residue 23391. -/
theorem bounds_15_23391 : exactInterval 15 23391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23391 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23391) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23391 : oddCount 23391 15 = 9 ∧ acceleratedOrbit 15 23391 = 14053 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23391 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23391) = 3 ^ 9 * m + 14053 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23391.1, data_15_23391.2]

/-- Complete interval computation for depth 15, residue 23392. -/
theorem bounds_15_23392 : exactInterval 15 23392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23392 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23392) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23392 : oddCount 23392 15 = 7 ∧ acceleratedOrbit 15 23392 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23392 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23392) = 3 ^ 7 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23392.1, data_15_23392.2]

/-- Complete interval computation for depth 15, residue 23393. -/
theorem bounds_15_23393 : exactInterval 15 23393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23393 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23393) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23393 : oddCount 23393 15 = 11 ∧ acceleratedOrbit 15 23393 = 126481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23393 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23393) = 3 ^ 11 * m + 126481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23393.1, data_15_23393.2]

/-- Complete interval computation for depth 15, residue 23394. -/
theorem bounds_15_23394 : exactInterval 15 23394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23394 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23394) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23394 : oddCount 23394 15 = 7 ∧ acceleratedOrbit 15 23394 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23394 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23394) = 3 ^ 7 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23394.1, data_15_23394.2]

/-- Complete interval computation for depth 15, residue 23395. -/
theorem bounds_15_23395 : exactInterval 15 23395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23395 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23395) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23395 : oddCount 23395 15 = 7 ∧ acceleratedOrbit 15 23395 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23395 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23395) = 3 ^ 7 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23395.1, data_15_23395.2]

end Collatz.Research.PassageAtlas.Batch0714
