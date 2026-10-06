import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0592

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 19365. -/
theorem bounds_15_19365 : exactInterval 15 19365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19365 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19365) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19365 : oddCount 19365 15 = 10 ∧ acceleratedOrbit 15 19365 = 34910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19365 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19365) = 3 ^ 10 * m + 34910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19365.1, data_15_19365.2]

/-- Complete interval computation for depth 15, residue 19366. -/
theorem bounds_15_19366 : exactInterval 15 19366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19366 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19366) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19366 : oddCount 19366 15 = 10 ∧ acceleratedOrbit 15 19366 = 34910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19366 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19366) = 3 ^ 10 * m + 34910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19366.1, data_15_19366.2]

/-- Complete interval computation for depth 15, residue 19367. -/
theorem bounds_15_19367 : exactInterval 15 19367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19367 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19367) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19367 : oddCount 19367 15 = 10 ∧ acceleratedOrbit 15 19367 = 34904 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19367 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19367) = 3 ^ 10 * m + 34904 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19367.1, data_15_19367.2]

/-- Complete interval computation for depth 15, residue 19368. -/
theorem bounds_15_19368 : exactInterval 15 19368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19368 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19368) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19368 : oddCount 19368 15 = 3 ∧ acceleratedOrbit 15 19368 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19368 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19368) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19368.1, data_15_19368.2]

/-- Complete interval computation for depth 15, residue 19369. -/
theorem bounds_15_19369 : exactInterval 15 19369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19369 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19369) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19369 : oddCount 19369 15 = 9 ∧ acceleratedOrbit 15 19369 = 11636 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19369 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19369) = 3 ^ 9 * m + 11636 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19369.1, data_15_19369.2]

/-- Complete interval computation for depth 15, residue 19370. -/
theorem bounds_15_19370 : exactInterval 15 19370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19370 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19370) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19370 : oddCount 19370 15 = 3 ∧ acceleratedOrbit 15 19370 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19370 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19370) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19370.1, data_15_19370.2]

/-- Complete interval computation for depth 15, residue 19371. -/
theorem bounds_15_19371 : exactInterval 15 19371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19371 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19371) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19371 : oddCount 19371 15 = 6 ∧ acceleratedOrbit 15 19371 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19371 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19371) = 3 ^ 6 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19371.1, data_15_19371.2]

/-- Complete interval computation for depth 15, residue 19372. -/
theorem bounds_15_19372 : exactInterval 15 19372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19372 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19372) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19372 : oddCount 19372 15 = 8 ∧ acceleratedOrbit 15 19372 = 3881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19372 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19372) = 3 ^ 8 * m + 3881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19372.1, data_15_19372.2]

/-- Complete interval computation for depth 15, residue 19373. -/
theorem bounds_15_19373 : exactInterval 15 19373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19373 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19373) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19373 : oddCount 19373 15 = 8 ∧ acceleratedOrbit 15 19373 = 3881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19373 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19373) = 3 ^ 8 * m + 3881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19373.1, data_15_19373.2]

/-- Complete interval computation for depth 15, residue 19374. -/
theorem bounds_15_19374 : exactInterval 15 19374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19374 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19374) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19374 : oddCount 19374 15 = 8 ∧ acceleratedOrbit 15 19374 = 3881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19374 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19374) = 3 ^ 8 * m + 3881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19374.1, data_15_19374.2]

/-- Complete interval computation for depth 15, residue 19375. -/
theorem bounds_15_19375 : exactInterval 15 19375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19375 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19375) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19375 : oddCount 19375 15 = 8 ∧ acceleratedOrbit 15 19375 = 3881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19375 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19375) = 3 ^ 8 * m + 3881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19375.1, data_15_19375.2]

/-- Complete interval computation for depth 15, residue 19376. -/
theorem bounds_15_19376 : exactInterval 15 19376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19376 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19376) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19376 : oddCount 19376 15 = 8 ∧ acceleratedOrbit 15 19376 = 3887 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19376 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19376) = 3 ^ 8 * m + 3887 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19376.1, data_15_19376.2]

/-- Complete interval computation for depth 15, residue 19377. -/
theorem bounds_15_19377 : exactInterval 15 19377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19377 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19377) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19377 : oddCount 19377 15 = 8 ∧ acceleratedOrbit 15 19377 = 3887 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19377 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19377) = 3 ^ 8 * m + 3887 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19377.1, data_15_19377.2]

/-- Complete interval computation for depth 15, residue 19378. -/
theorem bounds_15_19378 : exactInterval 15 19378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19378 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19378) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19378 : oddCount 19378 15 = 8 ∧ acceleratedOrbit 15 19378 = 3887 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19378 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19378) = 3 ^ 8 * m + 3887 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19378.1, data_15_19378.2]

/-- Complete interval computation for depth 15, residue 19379. -/
theorem bounds_15_19379 : exactInterval 15 19379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19379 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19379) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19379 : oddCount 19379 15 = 8 ∧ acceleratedOrbit 15 19379 = 3887 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19379 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19379) = 3 ^ 8 * m + 3887 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19379.1, data_15_19379.2]

/-- Complete interval computation for depth 15, residue 19380. -/
theorem bounds_15_19380 : exactInterval 15 19380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19380 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19380) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19380 : oddCount 19380 15 = 8 ∧ acceleratedOrbit 15 19380 = 3887 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19380 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19380) = 3 ^ 8 * m + 3887 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19380.1, data_15_19380.2]

/-- Complete interval computation for depth 15, residue 19381. -/
theorem bounds_15_19381 : exactInterval 15 19381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19381 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19381) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19381 : oddCount 19381 15 = 8 ∧ acceleratedOrbit 15 19381 = 3887 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19381 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19381) = 3 ^ 8 * m + 3887 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19381.1, data_15_19381.2]

/-- Complete interval computation for depth 15, residue 19382. -/
theorem bounds_15_19382 : exactInterval 15 19382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19382 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19382) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19382 : oddCount 19382 15 = 7 ∧ acceleratedOrbit 15 19382 = 1295 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19382 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19382) = 3 ^ 7 * m + 1295 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19382.1, data_15_19382.2]

/-- Complete interval computation for depth 15, residue 19383. -/
theorem bounds_15_19383 : exactInterval 15 19383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19383 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19383) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19383 : oddCount 19383 15 = 7 ∧ acceleratedOrbit 15 19383 = 1295 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19383 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19383) = 3 ^ 7 * m + 1295 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19383.1, data_15_19383.2]

/-- Complete interval computation for depth 15, residue 19384. -/
theorem bounds_15_19384 : exactInterval 15 19384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19384 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19384) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19384 : oddCount 19384 15 = 8 ∧ acceleratedOrbit 15 19384 = 3887 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19384 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19384) = 3 ^ 8 * m + 3887 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19384.1, data_15_19384.2]

/-- Complete interval computation for depth 15, residue 19385. -/
theorem bounds_15_19385 : exactInterval 15 19385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19385 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19385) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19385 : oddCount 19385 15 = 8 ∧ acceleratedOrbit 15 19385 = 3883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19385 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19385) = 3 ^ 8 * m + 3883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19385.1, data_15_19385.2]

/-- Complete interval computation for depth 15, residue 19386. -/
theorem bounds_15_19386 : exactInterval 15 19386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19386 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19386) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19386 : oddCount 19386 15 = 8 ∧ acceleratedOrbit 15 19386 = 3887 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19386 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19386) = 3 ^ 8 * m + 3887 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19386.1, data_15_19386.2]

/-- Complete interval computation for depth 15, residue 19387. -/
theorem bounds_15_19387 : exactInterval 15 19387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19387 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19387) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19387 : oddCount 19387 15 = 8 ∧ acceleratedOrbit 15 19387 = 3883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19387 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19387) = 3 ^ 8 * m + 3883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19387.1, data_15_19387.2]

/-- Complete interval computation for depth 15, residue 19388. -/
theorem bounds_15_19388 : exactInterval 15 19388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19388 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19388) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19388 : oddCount 19388 15 = 11 ∧ acceleratedOrbit 15 19388 = 104840 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19388 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19388) = 3 ^ 11 * m + 104840 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19388.1, data_15_19388.2]

/-- Complete interval computation for depth 15, residue 19389. -/
theorem bounds_15_19389 : exactInterval 15 19389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19389 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19389) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19389 : oddCount 19389 15 = 11 ∧ acceleratedOrbit 15 19389 = 104840 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19389 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19389) = 3 ^ 11 * m + 104840 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19389.1, data_15_19389.2]

/-- Complete interval computation for depth 15, residue 19390. -/
theorem bounds_15_19390 : exactInterval 15 19390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19390 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19390) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19390 : oddCount 19390 15 = 11 ∧ acceleratedOrbit 15 19390 = 104840 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19390 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19390) = 3 ^ 11 * m + 104840 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19390.1, data_15_19390.2]

/-- Complete interval computation for depth 15, residue 19391. -/
theorem bounds_15_19391 : exactInterval 15 19391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19391 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19391) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19391 : oddCount 19391 15 = 11 ∧ acceleratedOrbit 15 19391 = 104836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19391 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19391) = 3 ^ 11 * m + 104836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19391.1, data_15_19391.2]

/-- Complete interval computation for depth 15, residue 19392. -/
theorem bounds_15_19392 : exactInterval 15 19392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19392 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19392) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19392 : oddCount 19392 15 = 6 ∧ acceleratedOrbit 15 19392 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19392 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19392) = 3 ^ 6 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19392.1, data_15_19392.2]

/-- Complete interval computation for depth 15, residue 19393. -/
theorem bounds_15_19393 : exactInterval 15 19393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19393 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19393) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19393 : oddCount 19393 15 = 9 ∧ acceleratedOrbit 15 19393 = 11654 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19393 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19393) = 3 ^ 9 * m + 11654 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19393.1, data_15_19393.2]

/-- Complete interval computation for depth 15, residue 19394. -/
theorem bounds_15_19394 : exactInterval 15 19394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19394 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19394) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19394 : oddCount 19394 15 = 9 ∧ acceleratedOrbit 15 19394 = 11654 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19394 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19394) = 3 ^ 9 * m + 11654 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19394.1, data_15_19394.2]

/-- Complete interval computation for depth 15, residue 19395. -/
theorem bounds_15_19395 : exactInterval 15 19395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19395 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19395) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19395 : oddCount 19395 15 = 9 ∧ acceleratedOrbit 15 19395 = 11654 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19395 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19395) = 3 ^ 9 * m + 11654 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19395.1, data_15_19395.2]

/-- Complete interval computation for depth 15, residue 19396. -/
theorem bounds_15_19396 : exactInterval 15 19396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19396 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19396) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19396 : oddCount 19396 15 = 3 ∧ acceleratedOrbit 15 19396 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19396 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19396) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19396.1, data_15_19396.2]

/-- Complete interval computation for depth 15, residue 19397. -/
theorem bounds_15_19397 : exactInterval 15 19397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19397 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19397) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19397 : oddCount 19397 15 = 3 ∧ acceleratedOrbit 15 19397 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19397 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19397) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19397.1, data_15_19397.2]

end Collatz.Research.PassageAtlas.Batch0592
