import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0778

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 25460. -/
theorem bounds_15_25460 : exactInterval 15 25460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25460 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25460) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25460 : oddCount 25460 15 = 9 ∧ acceleratedOrbit 15 25460 = 15308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25460 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25460) = 3 ^ 9 * m + 15308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25460.1, data_15_25460.2]

/-- Complete interval computation for depth 15, residue 25461. -/
theorem bounds_15_25461 : exactInterval 15 25461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25461 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25461) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25461 : oddCount 25461 15 = 9 ∧ acceleratedOrbit 15 25461 = 15308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25461 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25461) = 3 ^ 9 * m + 15308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25461.1, data_15_25461.2]

/-- Complete interval computation for depth 15, residue 25462. -/
theorem bounds_15_25462 : exactInterval 15 25462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25462 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25462) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25462 : oddCount 25462 15 = 9 ∧ acceleratedOrbit 15 25462 = 15299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25462 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25462) = 3 ^ 9 * m + 15299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25462.1, data_15_25462.2]

/-- Complete interval computation for depth 15, residue 25463. -/
theorem bounds_15_25463 : exactInterval 15 25463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25463 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25463) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25463 : oddCount 25463 15 = 9 ∧ acceleratedOrbit 15 25463 = 15299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25463 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25463) = 3 ^ 9 * m + 15299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25463.1, data_15_25463.2]

/-- Complete interval computation for depth 15, residue 25464. -/
theorem bounds_15_25464 : exactInterval 15 25464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25464 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25464) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25464 : oddCount 25464 15 = 9 ∧ acceleratedOrbit 15 25464 = 15302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25464 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25464) = 3 ^ 9 * m + 15302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25464.1, data_15_25464.2]

/-- Complete interval computation for depth 15, residue 25465. -/
theorem bounds_15_25465 : exactInterval 15 25465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25465 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25465) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25465 : oddCount 25465 15 = 10 ∧ acceleratedOrbit 15 25465 = 45893 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25465 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25465) = 3 ^ 10 * m + 45893 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25465.1, data_15_25465.2]

/-- Complete interval computation for depth 15, residue 25466. -/
theorem bounds_15_25466 : exactInterval 15 25466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25466 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25466) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25466 : oddCount 25466 15 = 9 ∧ acceleratedOrbit 15 25466 = 15302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25466 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25466) = 3 ^ 9 * m + 15302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25466.1, data_15_25466.2]

/-- Complete interval computation for depth 15, residue 25467. -/
theorem bounds_15_25467 : exactInterval 15 25467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25467 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25467) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25467 : oddCount 25467 15 = 11 ∧ acceleratedOrbit 15 25467 = 137690 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25467 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25467) = 3 ^ 11 * m + 137690 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25467.1, data_15_25467.2]

/-- Complete interval computation for depth 15, residue 25468. -/
theorem bounds_15_25468 : exactInterval 15 25468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25468 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25468) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25468 : oddCount 25468 15 = 9 ∧ acceleratedOrbit 15 25468 = 15302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25468 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25468) = 3 ^ 9 * m + 15302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25468.1, data_15_25468.2]

/-- Complete interval computation for depth 15, residue 25469. -/
theorem bounds_15_25469 : exactInterval 15 25469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25469 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25469) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25469 : oddCount 25469 15 = 9 ∧ acceleratedOrbit 15 25469 = 15302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25469 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25469) = 3 ^ 9 * m + 15302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25469.1, data_15_25469.2]

/-- Complete interval computation for depth 15, residue 25470. -/
theorem bounds_15_25470 : exactInterval 15 25470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25470 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25470) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25470 : oddCount 25470 15 = 10 ∧ acceleratedOrbit 15 25470 = 45902 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25470 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25470) = 3 ^ 10 * m + 45902 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25470.1, data_15_25470.2]

/-- Complete interval computation for depth 15, residue 25471. -/
theorem bounds_15_25471 : exactInterval 15 25471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25471 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25471) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25471 : oddCount 25471 15 = 10 ∧ acceleratedOrbit 15 25471 = 45902 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25471 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25471) = 3 ^ 10 * m + 45902 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25471.1, data_15_25471.2]

/-- Complete interval computation for depth 15, residue 25472. -/
theorem bounds_15_25472 : exactInterval 15 25472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25472 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25472) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25472 : oddCount 25472 15 = 5 ∧ acceleratedOrbit 15 25472 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25472 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25472) = 3 ^ 5 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25472.1, data_15_25472.2]

/-- Complete interval computation for depth 15, residue 25473. -/
theorem bounds_15_25473 : exactInterval 15 25473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25473 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25473) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25473 : oddCount 25473 15 = 9 ∧ acceleratedOrbit 15 25473 = 15304 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25473 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25473) = 3 ^ 9 * m + 15304 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25473.1, data_15_25473.2]

/-- Complete interval computation for depth 15, residue 25474. -/
theorem bounds_15_25474 : exactInterval 15 25474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25474 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25474) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25474 : oddCount 25474 15 = 10 ∧ acceleratedOrbit 15 25474 = 45926 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25474 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25474) = 3 ^ 10 * m + 45926 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25474.1, data_15_25474.2]

/-- Complete interval computation for depth 15, residue 25475. -/
theorem bounds_15_25475 : exactInterval 15 25475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25475 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25475) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25475 : oddCount 25475 15 = 10 ∧ acceleratedOrbit 15 25475 = 45926 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25475 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25475) = 3 ^ 10 * m + 45926 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25475.1, data_15_25475.2]

/-- Complete interval computation for depth 15, residue 25476. -/
theorem bounds_15_25476 : exactInterval 15 25476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25476 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25476) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25476 : oddCount 25476 15 = 11 ∧ acceleratedOrbit 15 25476 = 137780 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25476 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25476) = 3 ^ 11 * m + 137780 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25476.1, data_15_25476.2]

/-- Complete interval computation for depth 15, residue 25477. -/
theorem bounds_15_25477 : exactInterval 15 25477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25477 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25477) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25477 : oddCount 25477 15 = 11 ∧ acceleratedOrbit 15 25477 = 137780 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25477 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25477) = 3 ^ 11 * m + 137780 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25477.1, data_15_25477.2]

/-- Complete interval computation for depth 15, residue 25478. -/
theorem bounds_15_25478 : exactInterval 15 25478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25478 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25478) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25478 : oddCount 25478 15 = 11 ∧ acceleratedOrbit 15 25478 = 137780 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25478 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25478) = 3 ^ 11 * m + 137780 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25478.1, data_15_25478.2]

/-- Complete interval computation for depth 15, residue 25479. -/
theorem bounds_15_25479 : exactInterval 15 25479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25479 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25479) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25479 : oddCount 25479 15 = 10 ∧ acceleratedOrbit 15 25479 = 45926 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25479 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25479) = 3 ^ 10 * m + 45926 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25479.1, data_15_25479.2]

/-- Complete interval computation for depth 15, residue 25480. -/
theorem bounds_15_25480 : exactInterval 15 25480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25480 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25480) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25480 : oddCount 25480 15 = 2 ∧ acceleratedOrbit 15 25480 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25480 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25480) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25480.1, data_15_25480.2]

/-- Complete interval computation for depth 15, residue 25481. -/
theorem bounds_15_25481 : exactInterval 15 25481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25481 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25481) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25481 : oddCount 25481 15 = 10 ∧ acceleratedOrbit 15 25481 = 45922 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25481 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25481) = 3 ^ 10 * m + 45922 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25481.1, data_15_25481.2]

/-- Complete interval computation for depth 15, residue 25482. -/
theorem bounds_15_25482 : exactInterval 15 25482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25482 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25482) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25482 : oddCount 25482 15 = 2 ∧ acceleratedOrbit 15 25482 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25482 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25482) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25482.1, data_15_25482.2]

/-- Complete interval computation for depth 15, residue 25483. -/
theorem bounds_15_25483 : exactInterval 15 25483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25483 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25483) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25483 : oddCount 25483 15 = 12 ∧ acceleratedOrbit 15 25483 = 413342 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25483 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25483) = 3 ^ 12 * m + 413342 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25483.1, data_15_25483.2]

/-- Complete interval computation for depth 15, residue 25484. -/
theorem bounds_15_25484 : exactInterval 15 25484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25484 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25484) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25484 : oddCount 25484 15 = 2 ∧ acceleratedOrbit 15 25484 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25484 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25484) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25484.1, data_15_25484.2]

/-- Complete interval computation for depth 15, residue 25485. -/
theorem bounds_15_25485 : exactInterval 15 25485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25485 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25485) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25485 : oddCount 25485 15 = 2 ∧ acceleratedOrbit 15 25485 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25485 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25485) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25485.1, data_15_25485.2]

/-- Complete interval computation for depth 15, residue 25486. -/
theorem bounds_15_25486 : exactInterval 15 25486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25486 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25486) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25486 : oddCount 25486 15 = 8 ∧ acceleratedOrbit 15 25486 = 5104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25486 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25486) = 3 ^ 8 * m + 5104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25486.1, data_15_25486.2]

/-- Complete interval computation for depth 15, residue 25487. -/
theorem bounds_15_25487 : exactInterval 15 25487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25487 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25487) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25487 : oddCount 25487 15 = 8 ∧ acceleratedOrbit 15 25487 = 5104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25487 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25487) = 3 ^ 8 * m + 5104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25487.1, data_15_25487.2]

/-- Complete interval computation for depth 15, residue 25488. -/
theorem bounds_15_25488 : exactInterval 15 25488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25488 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25488) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25488 : oddCount 25488 15 = 6 ∧ acceleratedOrbit 15 25488 = 568 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25488 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25488) = 3 ^ 6 * m + 568 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25488.1, data_15_25488.2]

/-- Complete interval computation for depth 15, residue 25489. -/
theorem bounds_15_25489 : exactInterval 15 25489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25489 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25489) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25489 : oddCount 25489 15 = 7 ∧ acceleratedOrbit 15 25489 = 1702 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25489 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25489) = 3 ^ 7 * m + 1702 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25489.1, data_15_25489.2]

/-- Complete interval computation for depth 15, residue 25490. -/
theorem bounds_15_25490 : exactInterval 15 25490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25490 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25490) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25490 : oddCount 25490 15 = 7 ∧ acceleratedOrbit 15 25490 = 1702 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25490 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25490) = 3 ^ 7 * m + 1702 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25490.1, data_15_25490.2]

/-- Complete interval computation for depth 15, residue 25491. -/
theorem bounds_15_25491 : exactInterval 15 25491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25491 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25491) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25491 : oddCount 25491 15 = 7 ∧ acceleratedOrbit 15 25491 = 1702 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25491 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25491) = 3 ^ 7 * m + 1702 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25491.1, data_15_25491.2]

/-- Complete interval computation for depth 15, residue 25492. -/
theorem bounds_15_25492 : exactInterval 15 25492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25492 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25492) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25492 : oddCount 25492 15 = 6 ∧ acceleratedOrbit 15 25492 = 568 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25492 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25492) = 3 ^ 6 * m + 568 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25492.1, data_15_25492.2]

end Collatz.Research.PassageAtlas.Batch0778
