import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0470

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 15368. -/
theorem bounds_15_15368 : exactInterval 15 15368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15368 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15368) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15368 : oddCount 15368 15 = 7 ∧ acceleratedOrbit 15 15368 = 1028 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15368 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15368) = 3 ^ 7 * m + 1028 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15368.1, data_15_15368.2]

/-- Complete interval computation for depth 15, residue 15369. -/
theorem bounds_15_15369 : exactInterval 15 15369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15369 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15369) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15369 : oddCount 15369 15 = 11 ∧ acceleratedOrbit 15 15369 = 83105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15369 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15369) = 3 ^ 11 * m + 83105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15369.1, data_15_15369.2]

/-- Complete interval computation for depth 15, residue 15370. -/
theorem bounds_15_15370 : exactInterval 15 15370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15370 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15370) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15370 : oddCount 15370 15 = 7 ∧ acceleratedOrbit 15 15370 = 1028 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15370 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15370) = 3 ^ 7 * m + 1028 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15370.1, data_15_15370.2]

/-- Complete interval computation for depth 15, residue 15371. -/
theorem bounds_15_15371 : exactInterval 15 15371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15371 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15371) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15371 : oddCount 15371 15 = 4 ∧ acceleratedOrbit 15 15371 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15371 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15371) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15371.1, data_15_15371.2]

/-- Complete interval computation for depth 15, residue 15372. -/
theorem bounds_15_15372 : exactInterval 15 15372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15372 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15372) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15372 : oddCount 15372 15 = 7 ∧ acceleratedOrbit 15 15372 = 1028 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15372 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15372) = 3 ^ 7 * m + 1028 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15372.1, data_15_15372.2]

/-- Complete interval computation for depth 15, residue 15373. -/
theorem bounds_15_15373 : exactInterval 15 15373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15373 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15373) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15373 : oddCount 15373 15 = 7 ∧ acceleratedOrbit 15 15373 = 1028 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15373 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15373) = 3 ^ 7 * m + 1028 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15373.1, data_15_15373.2]

/-- Complete interval computation for depth 15, residue 15374. -/
theorem bounds_15_15374 : exactInterval 15 15374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15374 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15374) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15374 : oddCount 15374 15 = 8 ∧ acceleratedOrbit 15 15374 = 3080 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15374 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15374) = 3 ^ 8 * m + 3080 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15374.1, data_15_15374.2]

/-- Complete interval computation for depth 15, residue 15375. -/
theorem bounds_15_15375 : exactInterval 15 15375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15375 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15375) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15375 : oddCount 15375 15 = 8 ∧ acceleratedOrbit 15 15375 = 3080 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15375 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15375) = 3 ^ 8 * m + 3080 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15375.1, data_15_15375.2]

/-- Complete interval computation for depth 15, residue 15376. -/
theorem bounds_15_15376 : exactInterval 15 15376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15376 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15376) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15376 : oddCount 15376 15 = 6 ∧ acceleratedOrbit 15 15376 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15376 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15376) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15376.1, data_15_15376.2]

/-- Complete interval computation for depth 15, residue 15377. -/
theorem bounds_15_15377 : exactInterval 15 15377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15377 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15377) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15377 : oddCount 15377 15 = 7 ∧ acceleratedOrbit 15 15377 = 1028 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15377 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15377) = 3 ^ 7 * m + 1028 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15377.1, data_15_15377.2]

/-- Complete interval computation for depth 15, residue 15378. -/
theorem bounds_15_15378 : exactInterval 15 15378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15378 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15378) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15378 : oddCount 15378 15 = 7 ∧ acceleratedOrbit 15 15378 = 1027 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15378 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15378) = 3 ^ 7 * m + 1027 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15378.1, data_15_15378.2]

/-- Complete interval computation for depth 15, residue 15379. -/
theorem bounds_15_15379 : exactInterval 15 15379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15379 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15379) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15379 : oddCount 15379 15 = 7 ∧ acceleratedOrbit 15 15379 = 1027 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15379 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15379) = 3 ^ 7 * m + 1027 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15379.1, data_15_15379.2]

/-- Complete interval computation for depth 15, residue 15380. -/
theorem bounds_15_15380 : exactInterval 15 15380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15380 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15380) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15380 : oddCount 15380 15 = 6 ∧ acceleratedOrbit 15 15380 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15380 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15380) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15380.1, data_15_15380.2]

/-- Complete interval computation for depth 15, residue 15381. -/
theorem bounds_15_15381 : exactInterval 15 15381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15381 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15381) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15381 : oddCount 15381 15 = 6 ∧ acceleratedOrbit 15 15381 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15381 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15381) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15381.1, data_15_15381.2]

/-- Complete interval computation for depth 15, residue 15382. -/
theorem bounds_15_15382 : exactInterval 15 15382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15382 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15382) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15382 : oddCount 15382 15 = 7 ∧ acceleratedOrbit 15 15382 = 1028 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15382 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15382) = 3 ^ 7 * m + 1028 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15382.1, data_15_15382.2]

/-- Complete interval computation for depth 15, residue 15383. -/
theorem bounds_15_15383 : exactInterval 15 15383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15383 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15383) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15383 : oddCount 15383 15 = 7 ∧ acceleratedOrbit 15 15383 = 1028 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15383 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15383) = 3 ^ 7 * m + 1028 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15383.1, data_15_15383.2]

/-- Complete interval computation for depth 15, residue 15384. -/
theorem bounds_15_15384 : exactInterval 15 15384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15384 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15384) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15384 : oddCount 15384 15 = 6 ∧ acceleratedOrbit 15 15384 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15384 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15384) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15384.1, data_15_15384.2]

/-- Complete interval computation for depth 15, residue 15385. -/
theorem bounds_15_15385 : exactInterval 15 15385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15385 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15385) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15385 : oddCount 15385 15 = 9 ∧ acceleratedOrbit 15 15385 = 9244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15385 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15385) = 3 ^ 9 * m + 9244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15385.1, data_15_15385.2]

/-- Complete interval computation for depth 15, residue 15386. -/
theorem bounds_15_15386 : exactInterval 15 15386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15386 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15386) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15386 : oddCount 15386 15 = 6 ∧ acceleratedOrbit 15 15386 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15386 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15386) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15386.1, data_15_15386.2]

/-- Complete interval computation for depth 15, residue 15387. -/
theorem bounds_15_15387 : exactInterval 15 15387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15387 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15387) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15387 : oddCount 15387 15 = 10 ∧ acceleratedOrbit 15 15387 = 27731 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15387 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15387) = 3 ^ 10 * m + 27731 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15387.1, data_15_15387.2]

/-- Complete interval computation for depth 15, residue 15388. -/
theorem bounds_15_15388 : exactInterval 15 15388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15388 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15388) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15388 : oddCount 15388 15 = 7 ∧ acceleratedOrbit 15 15388 = 1028 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15388 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15388) = 3 ^ 7 * m + 1028 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15388.1, data_15_15388.2]

/-- Complete interval computation for depth 15, residue 15389. -/
theorem bounds_15_15389 : exactInterval 15 15389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15389 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15389) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15389 : oddCount 15389 15 = 7 ∧ acceleratedOrbit 15 15389 = 1028 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15389 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15389) = 3 ^ 7 * m + 1028 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15389.1, data_15_15389.2]

/-- Complete interval computation for depth 15, residue 15390. -/
theorem bounds_15_15390 : exactInterval 15 15390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15390 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15390) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15390 : oddCount 15390 15 = 7 ∧ acceleratedOrbit 15 15390 = 1028 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15390 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15390) = 3 ^ 7 * m + 1028 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15390.1, data_15_15390.2]

/-- Complete interval computation for depth 15, residue 15391. -/
theorem bounds_15_15391 : exactInterval 15 15391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15391 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15391) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15391 : oddCount 15391 15 = 11 ∧ acceleratedOrbit 15 15391 = 83213 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15391 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15391) = 3 ^ 11 * m + 83213 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15391.1, data_15_15391.2]

/-- Complete interval computation for depth 15, residue 15392. -/
theorem bounds_15_15392 : exactInterval 15 15392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15392 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15392) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15392 : oddCount 15392 15 = 6 ∧ acceleratedOrbit 15 15392 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15392 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15392) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15392.1, data_15_15392.2]

/-- Complete interval computation for depth 15, residue 15393. -/
theorem bounds_15_15393 : exactInterval 15 15393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15393 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15393) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15393 : oddCount 15393 15 = 8 ∧ acceleratedOrbit 15 15393 = 3083 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15393 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15393) = 3 ^ 8 * m + 3083 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15393.1, data_15_15393.2]

/-- Complete interval computation for depth 15, residue 15394. -/
theorem bounds_15_15394 : exactInterval 15 15394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15394 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15394) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15394 : oddCount 15394 15 = 6 ∧ acceleratedOrbit 15 15394 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15394 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15394) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15394.1, data_15_15394.2]

/-- Complete interval computation for depth 15, residue 15395. -/
theorem bounds_15_15395 : exactInterval 15 15395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15395 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15395) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15395 : oddCount 15395 15 = 6 ∧ acceleratedOrbit 15 15395 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15395 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15395) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15395.1, data_15_15395.2]

/-- Complete interval computation for depth 15, residue 15396. -/
theorem bounds_15_15396 : exactInterval 15 15396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15396 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15396) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15396 : oddCount 15396 15 = 9 ∧ acceleratedOrbit 15 15396 = 9254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15396 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15396) = 3 ^ 9 * m + 9254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15396.1, data_15_15396.2]

/-- Complete interval computation for depth 15, residue 15397. -/
theorem bounds_15_15397 : exactInterval 15 15397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15397 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15397) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15397 : oddCount 15397 15 = 9 ∧ acceleratedOrbit 15 15397 = 9254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15397 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15397) = 3 ^ 9 * m + 9254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15397.1, data_15_15397.2]

/-- Complete interval computation for depth 15, residue 15398. -/
theorem bounds_15_15398 : exactInterval 15 15398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15398 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15398) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15398 : oddCount 15398 15 = 9 ∧ acceleratedOrbit 15 15398 = 9254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15398 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15398) = 3 ^ 9 * m + 9254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15398.1, data_15_15398.2]

/-- Complete interval computation for depth 15, residue 15399. -/
theorem bounds_15_15399 : exactInterval 15 15399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15399 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15399) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15399 : oddCount 15399 15 = 7 ∧ acceleratedOrbit 15 15399 = 1028 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15399 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15399) = 3 ^ 7 * m + 1028 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15399.1, data_15_15399.2]

end Collatz.Research.PassageAtlas.Batch0470
