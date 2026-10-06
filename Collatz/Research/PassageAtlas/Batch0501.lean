import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0501

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 16384. -/
theorem bounds_15_16384 : exactInterval 15 16384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16384 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16384) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16384 : oddCount 16384 15 = 1 ∧ acceleratedOrbit 15 16384 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16384 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16384) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16384.1, data_15_16384.2]

/-- Complete interval computation for depth 15, residue 16385. -/
theorem bounds_15_16385 : exactInterval 15 16385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16385 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16385) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16385 : oddCount 16385 15 = 7 ∧ acceleratedOrbit 15 16385 = 1094 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16385 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16385) = 3 ^ 7 * m + 1094 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16385.1, data_15_16385.2]

/-- Complete interval computation for depth 15, residue 16386. -/
theorem bounds_15_16386 : exactInterval 15 16386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16386 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16386) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16386 : oddCount 16386 15 = 8 ∧ acceleratedOrbit 15 16386 = 3284 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16386 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16386) = 3 ^ 8 * m + 3284 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16386.1, data_15_16386.2]

/-- Complete interval computation for depth 15, residue 16387. -/
theorem bounds_15_16387 : exactInterval 15 16387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16387 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16387) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16387 : oddCount 16387 15 = 8 ∧ acceleratedOrbit 15 16387 = 3284 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16387 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16387) = 3 ^ 8 * m + 3284 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16387.1, data_15_16387.2]

/-- Complete interval computation for depth 15, residue 16388. -/
theorem bounds_15_16388 : exactInterval 15 16388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16388 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16388) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16388 : oddCount 16388 15 = 6 ∧ acceleratedOrbit 15 16388 = 365 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16388 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16388) = 3 ^ 6 * m + 365 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16388.1, data_15_16388.2]

/-- Complete interval computation for depth 15, residue 16389. -/
theorem bounds_15_16389 : exactInterval 15 16389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16389 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16389) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16389 : oddCount 16389 15 = 6 ∧ acceleratedOrbit 15 16389 = 365 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16389 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16389) = 3 ^ 6 * m + 365 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16389.1, data_15_16389.2]

/-- Complete interval computation for depth 15, residue 16390. -/
theorem bounds_15_16390 : exactInterval 15 16390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16390 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16390) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16390 : oddCount 16390 15 = 6 ∧ acceleratedOrbit 15 16390 = 365 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16390 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16390) = 3 ^ 6 * m + 365 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16390.1, data_15_16390.2]

/-- Complete interval computation for depth 15, residue 16391. -/
theorem bounds_15_16391 : exactInterval 15 16391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16391 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16391) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16391 : oddCount 16391 15 = 8 ∧ acceleratedOrbit 15 16391 = 3284 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16391 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16391) = 3 ^ 8 * m + 3284 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16391.1, data_15_16391.2]

/-- Complete interval computation for depth 15, residue 16392. -/
theorem bounds_15_16392 : exactInterval 15 16392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16392 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16392) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16392 : oddCount 16392 15 = 7 ∧ acceleratedOrbit 15 16392 = 1097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16392 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16392) = 3 ^ 7 * m + 1097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16392.1, data_15_16392.2]

/-- Complete interval computation for depth 15, residue 16393. -/
theorem bounds_15_16393 : exactInterval 15 16393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16393 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16393) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16393 : oddCount 16393 15 = 8 ∧ acceleratedOrbit 15 16393 = 3284 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16393 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16393) = 3 ^ 8 * m + 3284 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16393.1, data_15_16393.2]

/-- Complete interval computation for depth 15, residue 16394. -/
theorem bounds_15_16394 : exactInterval 15 16394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16394 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16394) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16394 : oddCount 16394 15 = 7 ∧ acceleratedOrbit 15 16394 = 1097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16394 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16394) = 3 ^ 7 * m + 1097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16394.1, data_15_16394.2]

/-- Complete interval computation for depth 15, residue 16395. -/
theorem bounds_15_16395 : exactInterval 15 16395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16395 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16395) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16395 : oddCount 16395 15 = 6 ∧ acceleratedOrbit 15 16395 = 365 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16395 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16395) = 3 ^ 6 * m + 365 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16395.1, data_15_16395.2]

/-- Complete interval computation for depth 15, residue 16396. -/
theorem bounds_15_16396 : exactInterval 15 16396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16396 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16396) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16396 : oddCount 16396 15 = 7 ∧ acceleratedOrbit 15 16396 = 1097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16396 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16396) = 3 ^ 7 * m + 1097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16396.1, data_15_16396.2]

/-- Complete interval computation for depth 15, residue 16397. -/
theorem bounds_15_16397 : exactInterval 15 16397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16397 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16397) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16397 : oddCount 16397 15 = 7 ∧ acceleratedOrbit 15 16397 = 1097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16397 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16397) = 3 ^ 7 * m + 1097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16397.1, data_15_16397.2]

/-- Complete interval computation for depth 15, residue 16398. -/
theorem bounds_15_16398 : exactInterval 15 16398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16398 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16398) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16398 : oddCount 16398 15 = 6 ∧ acceleratedOrbit 15 16398 = 365 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16398 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16398) = 3 ^ 6 * m + 365 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16398.1, data_15_16398.2]

/-- Complete interval computation for depth 15, residue 16399. -/
theorem bounds_15_16399 : exactInterval 15 16399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16399 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16399) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16399 : oddCount 16399 15 = 6 ∧ acceleratedOrbit 15 16399 = 365 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16399 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16399) = 3 ^ 6 * m + 365 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16399.1, data_15_16399.2]

/-- Complete interval computation for depth 15, residue 16400. -/
theorem bounds_15_16400 : exactInterval 15 16400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16400 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16400) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16400 : oddCount 16400 15 = 5 ∧ acceleratedOrbit 15 16400 = 122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16400 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16400) = 3 ^ 5 * m + 122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16400.1, data_15_16400.2]

/-- Complete interval computation for depth 15, residue 16401. -/
theorem bounds_15_16401 : exactInterval 15 16401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16401 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16401) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16401 : oddCount 16401 15 = 7 ∧ acceleratedOrbit 15 16401 = 1097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16401 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16401) = 3 ^ 7 * m + 1097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16401.1, data_15_16401.2]

/-- Complete interval computation for depth 15, residue 16402. -/
theorem bounds_15_16402 : exactInterval 15 16402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16402 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16402) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16402 : oddCount 16402 15 = 6 ∧ acceleratedOrbit 15 16402 = 365 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16402 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16402) = 3 ^ 6 * m + 365 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16402.1, data_15_16402.2]

/-- Complete interval computation for depth 15, residue 16403. -/
theorem bounds_15_16403 : exactInterval 15 16403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16403 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16403) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16403 : oddCount 16403 15 = 6 ∧ acceleratedOrbit 15 16403 = 365 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16403 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16403) = 3 ^ 6 * m + 365 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16403.1, data_15_16403.2]

/-- Complete interval computation for depth 15, residue 16404. -/
theorem bounds_15_16404 : exactInterval 15 16404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16404 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16404) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16404 : oddCount 16404 15 = 5 ∧ acceleratedOrbit 15 16404 = 122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16404 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16404) = 3 ^ 5 * m + 122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16404.1, data_15_16404.2]

/-- Complete interval computation for depth 15, residue 16405. -/
theorem bounds_15_16405 : exactInterval 15 16405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16405 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16405) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16405 : oddCount 16405 15 = 5 ∧ acceleratedOrbit 15 16405 = 122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16405 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16405) = 3 ^ 5 * m + 122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16405.1, data_15_16405.2]

/-- Complete interval computation for depth 15, residue 16406. -/
theorem bounds_15_16406 : exactInterval 15 16406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16406 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16406) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16406 : oddCount 16406 15 = 7 ∧ acceleratedOrbit 15 16406 = 1097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16406 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16406) = 3 ^ 7 * m + 1097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16406.1, data_15_16406.2]

/-- Complete interval computation for depth 15, residue 16407. -/
theorem bounds_15_16407 : exactInterval 15 16407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16407 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16407) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16407 : oddCount 16407 15 = 7 ∧ acceleratedOrbit 15 16407 = 1097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16407 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16407) = 3 ^ 7 * m + 1097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16407.1, data_15_16407.2]

/-- Complete interval computation for depth 15, residue 16408. -/
theorem bounds_15_16408 : exactInterval 15 16408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16408 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16408) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16408 : oddCount 16408 15 = 5 ∧ acceleratedOrbit 15 16408 = 122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16408 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16408) = 3 ^ 5 * m + 122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16408.1, data_15_16408.2]

/-- Complete interval computation for depth 15, residue 16409. -/
theorem bounds_15_16409 : exactInterval 15 16409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16409 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16409) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16409 : oddCount 16409 15 = 8 ∧ acceleratedOrbit 15 16409 = 3287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16409 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16409) = 3 ^ 8 * m + 3287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16409.1, data_15_16409.2]

/-- Complete interval computation for depth 15, residue 16410. -/
theorem bounds_15_16410 : exactInterval 15 16410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16410 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16410) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16410 : oddCount 16410 15 = 5 ∧ acceleratedOrbit 15 16410 = 122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16410 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16410) = 3 ^ 5 * m + 122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16410.1, data_15_16410.2]

/-- Complete interval computation for depth 15, residue 16411. -/
theorem bounds_15_16411 : exactInterval 15 16411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16411 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16411) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16411 : oddCount 16411 15 = 10 ∧ acceleratedOrbit 15 16411 = 29576 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16411 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16411) = 3 ^ 10 * m + 29576 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16411.1, data_15_16411.2]

/-- Complete interval computation for depth 15, residue 16412. -/
theorem bounds_15_16412 : exactInterval 15 16412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16412 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16412) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16412 : oddCount 16412 15 = 7 ∧ acceleratedOrbit 15 16412 = 1097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16412 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16412) = 3 ^ 7 * m + 1097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16412.1, data_15_16412.2]

/-- Complete interval computation for depth 15, residue 16413. -/
theorem bounds_15_16413 : exactInterval 15 16413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16413 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16413) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16413 : oddCount 16413 15 = 7 ∧ acceleratedOrbit 15 16413 = 1097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16413 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16413) = 3 ^ 7 * m + 1097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16413.1, data_15_16413.2]

/-- Complete interval computation for depth 15, residue 16414. -/
theorem bounds_15_16414 : exactInterval 15 16414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16414 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16414) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16414 : oddCount 16414 15 = 7 ∧ acceleratedOrbit 15 16414 = 1097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16414 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16414) = 3 ^ 7 * m + 1097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16414.1, data_15_16414.2]

/-- Complete interval computation for depth 15, residue 16415. -/
theorem bounds_15_16415 : exactInterval 15 16415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16415 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16415) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16415 : oddCount 16415 15 = 12 ∧ acceleratedOrbit 15 16415 = 266246 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16415 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16415) = 3 ^ 12 * m + 266246 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16415.1, data_15_16415.2]

end Collatz.Research.PassageAtlas.Batch0501
