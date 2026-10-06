import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0379

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 12386. -/
theorem bounds_15_12386 : exactInterval 15 12386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12386 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12386) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12386 : oddCount 12386 15 = 9 ∧ acceleratedOrbit 15 12386 = 7451 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12386 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12386) = 3 ^ 9 * m + 7451 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12386.1, data_15_12386.2]

/-- Complete interval computation for depth 15, residue 12387. -/
theorem bounds_15_12387 : exactInterval 15 12387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12387 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12387) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12387 : oddCount 12387 15 = 9 ∧ acceleratedOrbit 15 12387 = 7451 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12387 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12387) = 3 ^ 9 * m + 7451 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12387.1, data_15_12387.2]

/-- Complete interval computation for depth 15, residue 12388. -/
theorem bounds_15_12388 : exactInterval 15 12388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12388 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12388) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12388 : oddCount 12388 15 = 9 ∧ acceleratedOrbit 15 12388 = 7451 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12388 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12388) = 3 ^ 9 * m + 7451 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12388.1, data_15_12388.2]

/-- Complete interval computation for depth 15, residue 12389. -/
theorem bounds_15_12389 : exactInterval 15 12389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12389 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12389) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12389 : oddCount 12389 15 = 9 ∧ acceleratedOrbit 15 12389 = 7451 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12389 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12389) = 3 ^ 9 * m + 7451 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12389.1, data_15_12389.2]

/-- Complete interval computation for depth 15, residue 12390. -/
theorem bounds_15_12390 : exactInterval 15 12390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12390 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12390) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12390 : oddCount 12390 15 = 9 ∧ acceleratedOrbit 15 12390 = 7451 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12390 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12390) = 3 ^ 9 * m + 7451 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12390.1, data_15_12390.2]

/-- Complete interval computation for depth 15, residue 12391. -/
theorem bounds_15_12391 : exactInterval 15 12391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12391 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12391) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12391 : oddCount 12391 15 = 9 ∧ acceleratedOrbit 15 12391 = 7444 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12391 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12391) = 3 ^ 9 * m + 7444 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12391.1, data_15_12391.2]

/-- Complete interval computation for depth 15, residue 12392. -/
theorem bounds_15_12392 : exactInterval 15 12392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12392 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12392) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12392 : oddCount 12392 15 = 4 ∧ acceleratedOrbit 15 12392 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12392 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12392) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12392.1, data_15_12392.2]

/-- Complete interval computation for depth 15, residue 12393. -/
theorem bounds_15_12393 : exactInterval 15 12393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12393 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12393) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12393 : oddCount 12393 15 = 8 ∧ acceleratedOrbit 15 12393 = 2483 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12393 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12393) = 3 ^ 8 * m + 2483 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12393.1, data_15_12393.2]

/-- Complete interval computation for depth 15, residue 12394. -/
theorem bounds_15_12394 : exactInterval 15 12394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12394 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12394) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12394 : oddCount 12394 15 = 4 ∧ acceleratedOrbit 15 12394 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12394 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12394) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12394.1, data_15_12394.2]

/-- Complete interval computation for depth 15, residue 12395. -/
theorem bounds_15_12395 : exactInterval 15 12395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12395 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12395) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12395 : oddCount 12395 15 = 9 ∧ acceleratedOrbit 15 12395 = 7447 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12395 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12395) = 3 ^ 9 * m + 7447 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12395.1, data_15_12395.2]

/-- Complete interval computation for depth 15, residue 12396. -/
theorem bounds_15_12396 : exactInterval 15 12396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12396 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12396) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12396 : oddCount 12396 15 = 10 ∧ acceleratedOrbit 15 12396 = 22349 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12396 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12396) = 3 ^ 10 * m + 22349 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12396.1, data_15_12396.2]

/-- Complete interval computation for depth 15, residue 12397. -/
theorem bounds_15_12397 : exactInterval 15 12397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12397 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12397) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12397 : oddCount 12397 15 = 10 ∧ acceleratedOrbit 15 12397 = 22349 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12397 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12397) = 3 ^ 10 * m + 22349 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12397.1, data_15_12397.2]

/-- Complete interval computation for depth 15, residue 12398. -/
theorem bounds_15_12398 : exactInterval 15 12398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12398 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12398) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12398 : oddCount 12398 15 = 10 ∧ acceleratedOrbit 15 12398 = 22349 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12398 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12398) = 3 ^ 10 * m + 22349 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12398.1, data_15_12398.2]

/-- Complete interval computation for depth 15, residue 12399. -/
theorem bounds_15_12399 : exactInterval 15 12399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12399 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12399) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12399 : oddCount 12399 15 = 12 ∧ acceleratedOrbit 15 12399 = 201113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12399 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12399) = 3 ^ 12 * m + 201113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12399.1, data_15_12399.2]

/-- Complete interval computation for depth 15, residue 12400. -/
theorem bounds_15_12400 : exactInterval 15 12400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12400 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12400) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12400 : oddCount 12400 15 = 7 ∧ acceleratedOrbit 15 12400 = 830 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12400 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12400) = 3 ^ 7 * m + 830 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12400.1, data_15_12400.2]

/-- Complete interval computation for depth 15, residue 12401. -/
theorem bounds_15_12401 : exactInterval 15 12401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12401 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12401) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12401 : oddCount 12401 15 = 4 ∧ acceleratedOrbit 15 12401 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12401 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12401) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12401.1, data_15_12401.2]

/-- Complete interval computation for depth 15, residue 12402. -/
theorem bounds_15_12402 : exactInterval 15 12402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12402 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12402) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12402 : oddCount 12402 15 = 5 ∧ acceleratedOrbit 15 12402 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12402 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12402) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12402.1, data_15_12402.2]

/-- Complete interval computation for depth 15, residue 12403. -/
theorem bounds_15_12403 : exactInterval 15 12403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12403 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12403) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12403 : oddCount 12403 15 = 5 ∧ acceleratedOrbit 15 12403 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12403 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12403) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12403.1, data_15_12403.2]

/-- Complete interval computation for depth 15, residue 12404. -/
theorem bounds_15_12404 : exactInterval 15 12404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12404 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12404) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12404 : oddCount 12404 15 = 7 ∧ acceleratedOrbit 15 12404 = 830 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12404 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12404) = 3 ^ 7 * m + 830 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12404.1, data_15_12404.2]

/-- Complete interval computation for depth 15, residue 12405. -/
theorem bounds_15_12405 : exactInterval 15 12405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12405 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12405) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12405 : oddCount 12405 15 = 7 ∧ acceleratedOrbit 15 12405 = 830 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12405 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12405) = 3 ^ 7 * m + 830 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12405.1, data_15_12405.2]

/-- Complete interval computation for depth 15, residue 12406. -/
theorem bounds_15_12406 : exactInterval 15 12406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12406 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12406) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12406 : oddCount 12406 15 = 8 ∧ acceleratedOrbit 15 12406 = 2486 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12406 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12406) = 3 ^ 8 * m + 2486 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12406.1, data_15_12406.2]

/-- Complete interval computation for depth 15, residue 12407. -/
theorem bounds_15_12407 : exactInterval 15 12407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12407 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12407) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12407 : oddCount 12407 15 = 8 ∧ acceleratedOrbit 15 12407 = 2486 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12407 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12407) = 3 ^ 8 * m + 2486 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12407.1, data_15_12407.2]

/-- Complete interval computation for depth 15, residue 12408. -/
theorem bounds_15_12408 : exactInterval 15 12408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12408 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12408) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12408 : oddCount 12408 15 = 7 ∧ acceleratedOrbit 15 12408 = 830 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12408 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12408) = 3 ^ 7 * m + 830 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12408.1, data_15_12408.2]

/-- Complete interval computation for depth 15, residue 12409. -/
theorem bounds_15_12409 : exactInterval 15 12409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12409 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12409) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12409 : oddCount 12409 15 = 10 ∧ acceleratedOrbit 15 12409 = 22366 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12409 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12409) = 3 ^ 10 * m + 22366 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12409.1, data_15_12409.2]

/-- Complete interval computation for depth 15, residue 12410. -/
theorem bounds_15_12410 : exactInterval 15 12410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12410 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12410) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12410 : oddCount 12410 15 = 7 ∧ acceleratedOrbit 15 12410 = 830 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12410 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12410) = 3 ^ 7 * m + 830 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12410.1, data_15_12410.2]

/-- Complete interval computation for depth 15, residue 12411. -/
theorem bounds_15_12411 : exactInterval 15 12411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12411 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12411) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12411 : oddCount 12411 15 = 8 ∧ acceleratedOrbit 15 12411 = 2486 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12411 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12411) = 3 ^ 8 * m + 2486 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12411.1, data_15_12411.2]

/-- Complete interval computation for depth 15, residue 12412. -/
theorem bounds_15_12412 : exactInterval 15 12412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12412 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12412) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12412 : oddCount 12412 15 = 10 ∧ acceleratedOrbit 15 12412 = 22376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12412 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12412) = 3 ^ 10 * m + 22376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12412.1, data_15_12412.2]

/-- Complete interval computation for depth 15, residue 12413. -/
theorem bounds_15_12413 : exactInterval 15 12413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12413 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12413) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12413 : oddCount 12413 15 = 10 ∧ acceleratedOrbit 15 12413 = 22376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12413 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12413) = 3 ^ 10 * m + 22376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12413.1, data_15_12413.2]

/-- Complete interval computation for depth 15, residue 12414. -/
theorem bounds_15_12414 : exactInterval 15 12414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12414 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12414) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12414 : oddCount 12414 15 = 10 ∧ acceleratedOrbit 15 12414 = 22376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12414 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12414) = 3 ^ 10 * m + 22376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12414.1, data_15_12414.2]

/-- Complete interval computation for depth 15, residue 12415. -/
theorem bounds_15_12415 : exactInterval 15 12415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12415 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12415) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12415 : oddCount 12415 15 = 8 ∧ acceleratedOrbit 15 12415 = 2486 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12415 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12415) = 3 ^ 8 * m + 2486 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12415.1, data_15_12415.2]

/-- Complete interval computation for depth 15, residue 12416. -/
theorem bounds_15_12416 : exactInterval 15 12416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12416 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12416) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12416 : oddCount 12416 15 = 5 ∧ acceleratedOrbit 15 12416 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12416 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12416) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12416.1, data_15_12416.2]

/-- Complete interval computation for depth 15, residue 12417. -/
theorem bounds_15_12417 : exactInterval 15 12417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12417 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12417) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12417 : oddCount 12417 15 = 7 ∧ acceleratedOrbit 15 12417 = 829 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12417 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12417) = 3 ^ 7 * m + 829 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12417.1, data_15_12417.2]

/-- Complete interval computation for depth 15, residue 12418. -/
theorem bounds_15_12418 : exactInterval 15 12418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12418 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12418) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12418 : oddCount 12418 15 = 7 ∧ acceleratedOrbit 15 12418 = 830 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12418 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12418) = 3 ^ 7 * m + 830 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12418.1, data_15_12418.2]

end Collatz.Research.PassageAtlas.Batch0379
