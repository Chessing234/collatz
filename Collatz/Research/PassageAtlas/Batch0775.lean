import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0775

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 25362. -/
theorem bounds_15_25362 : exactInterval 15 25362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25362 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25362) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25362 : oddCount 25362 15 = 7 ∧ acceleratedOrbit 15 25362 = 1693 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25362 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25362) = 3 ^ 7 * m + 1693 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25362.1, data_15_25362.2]

/-- Complete interval computation for depth 15, residue 25363. -/
theorem bounds_15_25363 : exactInterval 15 25363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25363 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25363) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25363 : oddCount 25363 15 = 7 ∧ acceleratedOrbit 15 25363 = 1693 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25363 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25363) = 3 ^ 7 * m + 1693 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25363.1, data_15_25363.2]

/-- Complete interval computation for depth 15, residue 25364. -/
theorem bounds_15_25364 : exactInterval 15 25364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25364 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25364) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25364 : oddCount 25364 15 = 7 ∧ acceleratedOrbit 15 25364 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25364 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25364) = 3 ^ 7 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25364.1, data_15_25364.2]

/-- Complete interval computation for depth 15, residue 25365. -/
theorem bounds_15_25365 : exactInterval 15 25365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25365 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25365) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25365 : oddCount 25365 15 = 7 ∧ acceleratedOrbit 15 25365 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25365 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25365) = 3 ^ 7 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25365.1, data_15_25365.2]

/-- Complete interval computation for depth 15, residue 25366. -/
theorem bounds_15_25366 : exactInterval 15 25366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25366 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25366) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25366 : oddCount 25366 15 = 9 ∧ acceleratedOrbit 15 25366 = 15241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25366 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25366) = 3 ^ 9 * m + 15241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25366.1, data_15_25366.2]

/-- Complete interval computation for depth 15, residue 25367. -/
theorem bounds_15_25367 : exactInterval 15 25367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25367 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25367) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25367 : oddCount 25367 15 = 9 ∧ acceleratedOrbit 15 25367 = 15241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25367 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25367) = 3 ^ 9 * m + 15241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25367.1, data_15_25367.2]

/-- Complete interval computation for depth 15, residue 25368. -/
theorem bounds_15_25368 : exactInterval 15 25368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25368 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25368) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25368 : oddCount 25368 15 = 7 ∧ acceleratedOrbit 15 25368 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25368 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25368) = 3 ^ 7 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25368.1, data_15_25368.2]

/-- Complete interval computation for depth 15, residue 25369. -/
theorem bounds_15_25369 : exactInterval 15 25369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25369 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25369) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25369 : oddCount 25369 15 = 9 ∧ acceleratedOrbit 15 25369 = 15241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25369 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25369) = 3 ^ 9 * m + 15241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25369.1, data_15_25369.2]

/-- Complete interval computation for depth 15, residue 25370. -/
theorem bounds_15_25370 : exactInterval 15 25370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25370 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25370) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25370 : oddCount 25370 15 = 7 ∧ acceleratedOrbit 15 25370 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25370 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25370) = 3 ^ 7 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25370.1, data_15_25370.2]

/-- Complete interval computation for depth 15, residue 25371. -/
theorem bounds_15_25371 : exactInterval 15 25371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25371 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25371) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25371 : oddCount 25371 15 = 10 ∧ acceleratedOrbit 15 25371 = 45722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25371 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25371) = 3 ^ 10 * m + 45722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25371.1, data_15_25371.2]

/-- Complete interval computation for depth 15, residue 25372. -/
theorem bounds_15_25372 : exactInterval 15 25372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25372 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25372) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25372 : oddCount 25372 15 = 7 ∧ acceleratedOrbit 15 25372 = 1694 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25372 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25372) = 3 ^ 7 * m + 1694 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25372.1, data_15_25372.2]

/-- Complete interval computation for depth 15, residue 25373. -/
theorem bounds_15_25373 : exactInterval 15 25373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25373 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25373) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25373 : oddCount 25373 15 = 7 ∧ acceleratedOrbit 15 25373 = 1694 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25373 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25373) = 3 ^ 7 * m + 1694 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25373.1, data_15_25373.2]

/-- Complete interval computation for depth 15, residue 25374. -/
theorem bounds_15_25374 : exactInterval 15 25374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25374 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25374) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25374 : oddCount 25374 15 = 7 ∧ acceleratedOrbit 15 25374 = 1694 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25374 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25374) = 3 ^ 7 * m + 1694 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25374.1, data_15_25374.2]

/-- Complete interval computation for depth 15, residue 25375. -/
theorem bounds_15_25375 : exactInterval 15 25375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25375 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25375) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25375 : oddCount 25375 15 = 8 ∧ acceleratedOrbit 15 25375 = 5081 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25375 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25375) = 3 ^ 8 * m + 5081 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25375.1, data_15_25375.2]

/-- Complete interval computation for depth 15, residue 25376. -/
theorem bounds_15_25376 : exactInterval 15 25376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25376 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25376) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25376 : oddCount 25376 15 = 7 ∧ acceleratedOrbit 15 25376 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25376 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25376) = 3 ^ 7 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25376.1, data_15_25376.2]

/-- Complete interval computation for depth 15, residue 25377. -/
theorem bounds_15_25377 : exactInterval 15 25377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25377 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25377) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25377 : oddCount 25377 15 = 9 ∧ acceleratedOrbit 15 25377 = 15248 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25377 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25377) = 3 ^ 9 * m + 15248 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25377.1, data_15_25377.2]

/-- Complete interval computation for depth 15, residue 25378. -/
theorem bounds_15_25378 : exactInterval 15 25378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25378 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25378) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25378 : oddCount 25378 15 = 6 ∧ acceleratedOrbit 15 25378 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25378 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25378) = 3 ^ 6 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25378.1, data_15_25378.2]

/-- Complete interval computation for depth 15, residue 25379. -/
theorem bounds_15_25379 : exactInterval 15 25379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25379 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25379) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25379 : oddCount 25379 15 = 6 ∧ acceleratedOrbit 15 25379 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25379 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25379) = 3 ^ 6 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25379.1, data_15_25379.2]

/-- Complete interval computation for depth 15, residue 25380. -/
theorem bounds_15_25380 : exactInterval 15 25380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25380 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25380) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25380 : oddCount 25380 15 = 6 ∧ acceleratedOrbit 15 25380 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25380 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25380) = 3 ^ 6 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25380.1, data_15_25380.2]

/-- Complete interval computation for depth 15, residue 25381. -/
theorem bounds_15_25381 : exactInterval 15 25381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25381 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25381) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25381 : oddCount 25381 15 = 6 ∧ acceleratedOrbit 15 25381 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25381 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25381) = 3 ^ 6 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25381.1, data_15_25381.2]

/-- Complete interval computation for depth 15, residue 25382. -/
theorem bounds_15_25382 : exactInterval 15 25382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25382 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25382) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25382 : oddCount 25382 15 = 6 ∧ acceleratedOrbit 15 25382 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25382 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25382) = 3 ^ 6 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25382.1, data_15_25382.2]

/-- Complete interval computation for depth 15, residue 25383. -/
theorem bounds_15_25383 : exactInterval 15 25383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25383 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25383) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25383 : oddCount 25383 15 = 11 ∧ acceleratedOrbit 15 25383 = 137234 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25383 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25383) = 3 ^ 11 * m + 137234 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25383.1, data_15_25383.2]

/-- Complete interval computation for depth 15, residue 25384. -/
theorem bounds_15_25384 : exactInterval 15 25384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25384 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25384) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25384 : oddCount 25384 15 = 7 ∧ acceleratedOrbit 15 25384 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25384 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25384) = 3 ^ 7 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25384.1, data_15_25384.2]

/-- Complete interval computation for depth 15, residue 25385. -/
theorem bounds_15_25385 : exactInterval 15 25385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25385 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25385) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25385 : oddCount 25385 15 = 9 ∧ acceleratedOrbit 15 25385 = 15250 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25385 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25385) = 3 ^ 9 * m + 15250 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25385.1, data_15_25385.2]

/-- Complete interval computation for depth 15, residue 25386. -/
theorem bounds_15_25386 : exactInterval 15 25386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25386 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25386) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25386 : oddCount 25386 15 = 7 ∧ acceleratedOrbit 15 25386 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25386 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25386) = 3 ^ 7 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25386.1, data_15_25386.2]

/-- Complete interval computation for depth 15, residue 25387. -/
theorem bounds_15_25387 : exactInterval 15 25387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25387 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25387) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25387 : oddCount 25387 15 = 9 ∧ acceleratedOrbit 15 25387 = 15254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25387 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25387) = 3 ^ 9 * m + 15254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25387.1, data_15_25387.2]

/-- Complete interval computation for depth 15, residue 25388. -/
theorem bounds_15_25388 : exactInterval 15 25388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25388 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25388) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25388 : oddCount 25388 15 = 7 ∧ acceleratedOrbit 15 25388 = 1696 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25388 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25388) = 3 ^ 7 * m + 1696 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25388.1, data_15_25388.2]

/-- Complete interval computation for depth 15, residue 25389. -/
theorem bounds_15_25389 : exactInterval 15 25389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25389 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25389) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25389 : oddCount 25389 15 = 7 ∧ acceleratedOrbit 15 25389 = 1696 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25389 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25389) = 3 ^ 7 * m + 1696 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25389.1, data_15_25389.2]

/-- Complete interval computation for depth 15, residue 25390. -/
theorem bounds_15_25390 : exactInterval 15 25390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25390 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25390) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25390 : oddCount 25390 15 = 7 ∧ acceleratedOrbit 15 25390 = 1696 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25390 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25390) = 3 ^ 7 * m + 1696 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25390.1, data_15_25390.2]

/-- Complete interval computation for depth 15, residue 25391. -/
theorem bounds_15_25391 : exactInterval 15 25391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25391 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25391) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25391 : oddCount 25391 15 = 9 ∧ acceleratedOrbit 15 25391 = 15254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25391 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25391) = 3 ^ 9 * m + 15254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25391.1, data_15_25391.2]

/-- Complete interval computation for depth 15, residue 25392. -/
theorem bounds_15_25392 : exactInterval 15 25392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25392 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25392) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25392 : oddCount 25392 15 = 7 ∧ acceleratedOrbit 15 25392 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25392 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25392) = 3 ^ 7 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25392.1, data_15_25392.2]

/-- Complete interval computation for depth 15, residue 25393. -/
theorem bounds_15_25393 : exactInterval 15 25393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25393 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25393) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25393 : oddCount 25393 15 = 7 ∧ acceleratedOrbit 15 25393 = 1696 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25393 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25393) = 3 ^ 7 * m + 1696 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25393.1, data_15_25393.2]

/-- Complete interval computation for depth 15, residue 25394. -/
theorem bounds_15_25394 : exactInterval 15 25394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25394 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25394) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25394 : oddCount 25394 15 = 7 ∧ acceleratedOrbit 15 25394 = 1696 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25394 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25394) = 3 ^ 7 * m + 1696 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25394.1, data_15_25394.2]

end Collatz.Research.PassageAtlas.Batch0775
