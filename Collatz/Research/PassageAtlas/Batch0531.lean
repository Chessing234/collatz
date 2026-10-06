import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0531

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 17367. -/
theorem bounds_15_17367 : exactInterval 15 17367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17367 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17367) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17367 : oddCount 17367 15 = 11 ∧ acceleratedOrbit 15 17367 = 93905 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17367 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17367) = 3 ^ 11 * m + 93905 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17367.1, data_15_17367.2]

/-- Complete interval computation for depth 15, residue 17368. -/
theorem bounds_15_17368 : exactInterval 15 17368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17368 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17368) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17368 : oddCount 17368 15 = 8 ∧ acceleratedOrbit 15 17368 = 3482 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17368 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17368) = 3 ^ 8 * m + 3482 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17368.1, data_15_17368.2]

/-- Complete interval computation for depth 15, residue 17369. -/
theorem bounds_15_17369 : exactInterval 15 17369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17369 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17369) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17369 : oddCount 17369 15 = 4 ∧ acceleratedOrbit 15 17369 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17369 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17369) = 3 ^ 4 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17369.1, data_15_17369.2]

/-- Complete interval computation for depth 15, residue 17370. -/
theorem bounds_15_17370 : exactInterval 15 17370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17370 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17370) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17370 : oddCount 17370 15 = 8 ∧ acceleratedOrbit 15 17370 = 3482 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17370 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17370) = 3 ^ 8 * m + 3482 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17370.1, data_15_17370.2]

/-- Complete interval computation for depth 15, residue 17371. -/
theorem bounds_15_17371 : exactInterval 15 17371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17371 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17371) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17371 : oddCount 17371 15 = 7 ∧ acceleratedOrbit 15 17371 = 1160 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17371 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17371) = 3 ^ 7 * m + 1160 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17371.1, data_15_17371.2]

/-- Complete interval computation for depth 15, residue 17372. -/
theorem bounds_15_17372 : exactInterval 15 17372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17372 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17372) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17372 : oddCount 17372 15 = 8 ∧ acceleratedOrbit 15 17372 = 3482 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17372 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17372) = 3 ^ 8 * m + 3482 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17372.1, data_15_17372.2]

/-- Complete interval computation for depth 15, residue 17373. -/
theorem bounds_15_17373 : exactInterval 15 17373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17373 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17373) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17373 : oddCount 17373 15 = 8 ∧ acceleratedOrbit 15 17373 = 3482 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17373 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17373) = 3 ^ 8 * m + 3482 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17373.1, data_15_17373.2]

/-- Complete interval computation for depth 15, residue 17374. -/
theorem bounds_15_17374 : exactInterval 15 17374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17374 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17374) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17374 : oddCount 17374 15 = 10 ∧ acceleratedOrbit 15 17374 = 31313 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17374 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17374) = 3 ^ 10 * m + 31313 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17374.1, data_15_17374.2]

/-- Complete interval computation for depth 15, residue 17375. -/
theorem bounds_15_17375 : exactInterval 15 17375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17375 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17375) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17375 : oddCount 17375 15 = 10 ∧ acceleratedOrbit 15 17375 = 31313 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17375 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17375) = 3 ^ 10 * m + 31313 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17375.1, data_15_17375.2]

/-- Complete interval computation for depth 15, residue 17376. -/
theorem bounds_15_17376 : exactInterval 15 17376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17376 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17376) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17376 : oddCount 17376 15 = 7 ∧ acceleratedOrbit 15 17376 = 1162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17376 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17376) = 3 ^ 7 * m + 1162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17376.1, data_15_17376.2]

/-- Complete interval computation for depth 15, residue 17377. -/
theorem bounds_15_17377 : exactInterval 15 17377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17377 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17377) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17377 : oddCount 17377 15 = 11 ∧ acceleratedOrbit 15 17377 = 93959 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17377 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17377) = 3 ^ 11 * m + 93959 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17377.1, data_15_17377.2]

/-- Complete interval computation for depth 15, residue 17378. -/
theorem bounds_15_17378 : exactInterval 15 17378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17378 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17378) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17378 : oddCount 17378 15 = 4 ∧ acceleratedOrbit 15 17378 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17378 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17378) = 3 ^ 4 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17378.1, data_15_17378.2]

/-- Complete interval computation for depth 15, residue 17379. -/
theorem bounds_15_17379 : exactInterval 15 17379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17379 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17379) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17379 : oddCount 17379 15 = 4 ∧ acceleratedOrbit 15 17379 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17379 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17379) = 3 ^ 4 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17379.1, data_15_17379.2]

/-- Complete interval computation for depth 15, residue 17380. -/
theorem bounds_15_17380 : exactInterval 15 17380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17380 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17380) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17380 : oddCount 17380 15 = 9 ∧ acceleratedOrbit 15 17380 = 10448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17380 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17380) = 3 ^ 9 * m + 10448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17380.1, data_15_17380.2]

/-- Complete interval computation for depth 15, residue 17381. -/
theorem bounds_15_17381 : exactInterval 15 17381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17381 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17381) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17381 : oddCount 17381 15 = 9 ∧ acceleratedOrbit 15 17381 = 10448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17381 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17381) = 3 ^ 9 * m + 10448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17381.1, data_15_17381.2]

/-- Complete interval computation for depth 15, residue 17382. -/
theorem bounds_15_17382 : exactInterval 15 17382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17382 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17382) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17382 : oddCount 17382 15 = 9 ∧ acceleratedOrbit 15 17382 = 10448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17382 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17382) = 3 ^ 9 * m + 10448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17382.1, data_15_17382.2]

/-- Complete interval computation for depth 15, residue 17383. -/
theorem bounds_15_17383 : exactInterval 15 17383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17383 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17383) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17383 : oddCount 17383 15 = 8 ∧ acceleratedOrbit 15 17383 = 3482 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17383 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17383) = 3 ^ 8 * m + 3482 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17383.1, data_15_17383.2]

/-- Complete interval computation for depth 15, residue 17384. -/
theorem bounds_15_17384 : exactInterval 15 17384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17384 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17384) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17384 : oddCount 17384 15 = 7 ∧ acceleratedOrbit 15 17384 = 1162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17384 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17384) = 3 ^ 7 * m + 1162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17384.1, data_15_17384.2]

/-- Complete interval computation for depth 15, residue 17385. -/
theorem bounds_15_17385 : exactInterval 15 17385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17385 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17385) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17385 : oddCount 17385 15 = 12 ∧ acceleratedOrbit 15 17385 = 281987 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17385 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17385) = 3 ^ 12 * m + 281987 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17385.1, data_15_17385.2]

/-- Complete interval computation for depth 15, residue 17386. -/
theorem bounds_15_17386 : exactInterval 15 17386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17386 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17386) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17386 : oddCount 17386 15 = 7 ∧ acceleratedOrbit 15 17386 = 1162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17386 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17386) = 3 ^ 7 * m + 1162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17386.1, data_15_17386.2]

/-- Complete interval computation for depth 15, residue 17387. -/
theorem bounds_15_17387 : exactInterval 15 17387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17387 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17387) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17387 : oddCount 17387 15 = 10 ∧ acceleratedOrbit 15 17387 = 31337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17387 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17387) = 3 ^ 10 * m + 31337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17387.1, data_15_17387.2]

/-- Complete interval computation for depth 15, residue 17388. -/
theorem bounds_15_17388 : exactInterval 15 17388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17388 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17388) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17388 : oddCount 17388 15 = 11 ∧ acceleratedOrbit 15 17388 = 94040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17388 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17388) = 3 ^ 11 * m + 94040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17388.1, data_15_17388.2]

/-- Complete interval computation for depth 15, residue 17389. -/
theorem bounds_15_17389 : exactInterval 15 17389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17389 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17389) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17389 : oddCount 17389 15 = 11 ∧ acceleratedOrbit 15 17389 = 94040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17389 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17389) = 3 ^ 11 * m + 94040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17389.1, data_15_17389.2]

/-- Complete interval computation for depth 15, residue 17390. -/
theorem bounds_15_17390 : exactInterval 15 17390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17390 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17390) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17390 : oddCount 17390 15 = 11 ∧ acceleratedOrbit 15 17390 = 94040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17390 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17390) = 3 ^ 11 * m + 94040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17390.1, data_15_17390.2]

/-- Complete interval computation for depth 15, residue 17391. -/
theorem bounds_15_17391 : exactInterval 15 17391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17391 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17391) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17391 : oddCount 17391 15 = 10 ∧ acceleratedOrbit 15 17391 = 31342 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17391 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17391) = 3 ^ 10 * m + 31342 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17391.1, data_15_17391.2]

/-- Complete interval computation for depth 15, residue 17392. -/
theorem bounds_15_17392 : exactInterval 15 17392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17392 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17392) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17392 : oddCount 17392 15 = 7 ∧ acceleratedOrbit 15 17392 = 1162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17392 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17392) = 3 ^ 7 * m + 1162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17392.1, data_15_17392.2]

/-- Complete interval computation for depth 15, residue 17393. -/
theorem bounds_15_17393 : exactInterval 15 17393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17393 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17393) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17393 : oddCount 17393 15 = 7 ∧ acceleratedOrbit 15 17393 = 1162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17393 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17393) = 3 ^ 7 * m + 1162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17393.1, data_15_17393.2]

/-- Complete interval computation for depth 15, residue 17394. -/
theorem bounds_15_17394 : exactInterval 15 17394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17394 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17394) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17394 : oddCount 17394 15 = 8 ∧ acceleratedOrbit 15 17394 = 3484 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17394 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17394) = 3 ^ 8 * m + 3484 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17394.1, data_15_17394.2]

/-- Complete interval computation for depth 15, residue 17395. -/
theorem bounds_15_17395 : exactInterval 15 17395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17395 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17395) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17395 : oddCount 17395 15 = 8 ∧ acceleratedOrbit 15 17395 = 3484 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17395 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17395) = 3 ^ 8 * m + 3484 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17395.1, data_15_17395.2]

/-- Complete interval computation for depth 15, residue 17396. -/
theorem bounds_15_17396 : exactInterval 15 17396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17396 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17396) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17396 : oddCount 17396 15 = 7 ∧ acceleratedOrbit 15 17396 = 1162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17396 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17396) = 3 ^ 7 * m + 1162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17396.1, data_15_17396.2]

/-- Complete interval computation for depth 15, residue 17397. -/
theorem bounds_15_17397 : exactInterval 15 17397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17397 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17397) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17397 : oddCount 17397 15 = 7 ∧ acceleratedOrbit 15 17397 = 1162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17397 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17397) = 3 ^ 7 * m + 1162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17397.1, data_15_17397.2]

/-- Complete interval computation for depth 15, residue 17398. -/
theorem bounds_15_17398 : exactInterval 15 17398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17398 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17398) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17398 : oddCount 17398 15 = 8 ∧ acceleratedOrbit 15 17398 = 3485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17398 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17398) = 3 ^ 8 * m + 3485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17398.1, data_15_17398.2]

end Collatz.Research.PassageAtlas.Batch0531
