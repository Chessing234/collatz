import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0870

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 28475. -/
theorem bounds_15_28475 : exactInterval 15 28475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28475 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28475) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28475 : oddCount 28475 15 = 7 ∧ acceleratedOrbit 15 28475 = 1901 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28475 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28475) = 3 ^ 7 * m + 1901 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28475.1, data_15_28475.2]

/-- Complete interval computation for depth 15, residue 28476. -/
theorem bounds_15_28476 : exactInterval 15 28476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28476 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28476) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28476 : oddCount 28476 15 = 7 ∧ acceleratedOrbit 15 28476 = 1901 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28476 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28476) = 3 ^ 7 * m + 1901 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28476.1, data_15_28476.2]

/-- Complete interval computation for depth 15, residue 28477. -/
theorem bounds_15_28477 : exactInterval 15 28477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28477 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28477) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28477 : oddCount 28477 15 = 7 ∧ acceleratedOrbit 15 28477 = 1901 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28477 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28477) = 3 ^ 7 * m + 1901 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28477.1, data_15_28477.2]

/-- Complete interval computation for depth 15, residue 28478. -/
theorem bounds_15_28478 : exactInterval 15 28478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28478 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28478) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28478 : oddCount 28478 15 = 9 ∧ acceleratedOrbit 15 28478 = 17108 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28478 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28478) = 3 ^ 9 * m + 17108 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28478.1, data_15_28478.2]

/-- Complete interval computation for depth 15, residue 28479. -/
theorem bounds_15_28479 : exactInterval 15 28479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28479 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28479) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28479 : oddCount 28479 15 = 9 ∧ acceleratedOrbit 15 28479 = 17108 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28479 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28479) = 3 ^ 9 * m + 17108 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28479.1, data_15_28479.2]

/-- Complete interval computation for depth 15, residue 28480. -/
theorem bounds_15_28480 : exactInterval 15 28480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28480 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28480) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28480 : oddCount 28480 15 = 6 ∧ acceleratedOrbit 15 28480 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28480 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28480) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28480.1, data_15_28480.2]

/-- Complete interval computation for depth 15, residue 28481. -/
theorem bounds_15_28481 : exactInterval 15 28481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28481 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28481) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28481 : oddCount 28481 15 = 7 ∧ acceleratedOrbit 15 28481 = 1903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28481 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28481) = 3 ^ 7 * m + 1903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28481.1, data_15_28481.2]

/-- Complete interval computation for depth 15, residue 28482. -/
theorem bounds_15_28482 : exactInterval 15 28482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28482 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28482) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28482 : oddCount 28482 15 = 6 ∧ acceleratedOrbit 15 28482 = 634 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28482 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28482) = 3 ^ 6 * m + 634 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28482.1, data_15_28482.2]

/-- Complete interval computation for depth 15, residue 28483. -/
theorem bounds_15_28483 : exactInterval 15 28483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28483 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28483) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28483 : oddCount 28483 15 = 6 ∧ acceleratedOrbit 15 28483 = 634 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28483 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28483) = 3 ^ 6 * m + 634 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28483.1, data_15_28483.2]

/-- Complete interval computation for depth 15, residue 28484. -/
theorem bounds_15_28484 : exactInterval 15 28484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28484 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28484) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28484 : oddCount 28484 15 = 7 ∧ acceleratedOrbit 15 28484 = 1903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28484 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28484) = 3 ^ 7 * m + 1903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28484.1, data_15_28484.2]

/-- Complete interval computation for depth 15, residue 28485. -/
theorem bounds_15_28485 : exactInterval 15 28485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28485 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28485) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28485 : oddCount 28485 15 = 7 ∧ acceleratedOrbit 15 28485 = 1903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28485 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28485) = 3 ^ 7 * m + 1903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28485.1, data_15_28485.2]

/-- Complete interval computation for depth 15, residue 28486. -/
theorem bounds_15_28486 : exactInterval 15 28486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28486 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28486) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28486 : oddCount 28486 15 = 7 ∧ acceleratedOrbit 15 28486 = 1903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28486 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28486) = 3 ^ 7 * m + 1903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28486.1, data_15_28486.2]

/-- Complete interval computation for depth 15, residue 28487. -/
theorem bounds_15_28487 : exactInterval 15 28487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28487 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28487) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28487 : oddCount 28487 15 = 9 ∧ acceleratedOrbit 15 28487 = 17113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28487 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28487) = 3 ^ 9 * m + 17113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28487.1, data_15_28487.2]

/-- Complete interval computation for depth 15, residue 28488. -/
theorem bounds_15_28488 : exactInterval 15 28488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28488 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28488) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28488 : oddCount 28488 15 = 8 ∧ acceleratedOrbit 15 28488 = 5707 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28488 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28488) = 3 ^ 8 * m + 5707 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28488.1, data_15_28488.2]

/-- Complete interval computation for depth 15, residue 28489. -/
theorem bounds_15_28489 : exactInterval 15 28489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28489 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28489) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28489 : oddCount 28489 15 = 9 ∧ acceleratedOrbit 15 28489 = 17117 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28489 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28489) = 3 ^ 9 * m + 17117 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28489.1, data_15_28489.2]

/-- Complete interval computation for depth 15, residue 28490. -/
theorem bounds_15_28490 : exactInterval 15 28490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28490 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28490) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28490 : oddCount 28490 15 = 8 ∧ acceleratedOrbit 15 28490 = 5707 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28490 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28490) = 3 ^ 8 * m + 5707 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28490.1, data_15_28490.2]

/-- Complete interval computation for depth 15, residue 28491. -/
theorem bounds_15_28491 : exactInterval 15 28491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28491 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28491) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28491 : oddCount 28491 15 = 7 ∧ acceleratedOrbit 15 28491 = 1903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28491 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28491) = 3 ^ 7 * m + 1903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28491.1, data_15_28491.2]

/-- Complete interval computation for depth 15, residue 28492. -/
theorem bounds_15_28492 : exactInterval 15 28492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28492 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28492) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28492 : oddCount 28492 15 = 8 ∧ acceleratedOrbit 15 28492 = 5707 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28492 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28492) = 3 ^ 8 * m + 5707 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28492.1, data_15_28492.2]

/-- Complete interval computation for depth 15, residue 28493. -/
theorem bounds_15_28493 : exactInterval 15 28493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28493 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28493) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28493 : oddCount 28493 15 = 8 ∧ acceleratedOrbit 15 28493 = 5707 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28493 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28493) = 3 ^ 8 * m + 5707 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28493.1, data_15_28493.2]

/-- Complete interval computation for depth 15, residue 28494. -/
theorem bounds_15_28494 : exactInterval 15 28494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28494 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28494) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28494 : oddCount 28494 15 = 11 ∧ acceleratedOrbit 15 28494 = 154061 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28494 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28494) = 3 ^ 11 * m + 154061 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28494.1, data_15_28494.2]

/-- Complete interval computation for depth 15, residue 28495. -/
theorem bounds_15_28495 : exactInterval 15 28495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28495 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28495) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28495 : oddCount 28495 15 = 11 ∧ acceleratedOrbit 15 28495 = 154061 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28495 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28495) = 3 ^ 11 * m + 154061 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28495.1, data_15_28495.2]

/-- Complete interval computation for depth 15, residue 28496. -/
theorem bounds_15_28496 : exactInterval 15 28496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28496 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28496) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28496 : oddCount 28496 15 = 6 ∧ acceleratedOrbit 15 28496 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28496 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28496) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28496.1, data_15_28496.2]

/-- Complete interval computation for depth 15, residue 28497. -/
theorem bounds_15_28497 : exactInterval 15 28497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28497 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28497) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28497 : oddCount 28497 15 = 8 ∧ acceleratedOrbit 15 28497 = 5707 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28497 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28497) = 3 ^ 8 * m + 5707 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28497.1, data_15_28497.2]

/-- Complete interval computation for depth 15, residue 28498. -/
theorem bounds_15_28498 : exactInterval 15 28498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28498 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28498) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28498 : oddCount 28498 15 = 11 ∧ acceleratedOrbit 15 28498 = 154082 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28498 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28498) = 3 ^ 11 * m + 154082 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28498.1, data_15_28498.2]

/-- Complete interval computation for depth 15, residue 28499. -/
theorem bounds_15_28499 : exactInterval 15 28499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28499 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28499) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28499 : oddCount 28499 15 = 11 ∧ acceleratedOrbit 15 28499 = 154082 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28499 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28499) = 3 ^ 11 * m + 154082 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28499.1, data_15_28499.2]

/-- Complete interval computation for depth 15, residue 28500. -/
theorem bounds_15_28500 : exactInterval 15 28500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28500 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28500) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28500 : oddCount 28500 15 = 6 ∧ acceleratedOrbit 15 28500 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28500 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28500) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28500.1, data_15_28500.2]

/-- Complete interval computation for depth 15, residue 28501. -/
theorem bounds_15_28501 : exactInterval 15 28501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28501 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28501) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28501 : oddCount 28501 15 = 6 ∧ acceleratedOrbit 15 28501 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28501 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28501) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28501.1, data_15_28501.2]

/-- Complete interval computation for depth 15, residue 28502. -/
theorem bounds_15_28502 : exactInterval 15 28502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28502 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28502) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28502 : oddCount 28502 15 = 8 ∧ acceleratedOrbit 15 28502 = 5708 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28502 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28502) = 3 ^ 8 * m + 5708 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28502.1, data_15_28502.2]

/-- Complete interval computation for depth 15, residue 28503. -/
theorem bounds_15_28503 : exactInterval 15 28503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28503 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28503) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28503 : oddCount 28503 15 = 8 ∧ acceleratedOrbit 15 28503 = 5708 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28503 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28503) = 3 ^ 8 * m + 5708 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28503.1, data_15_28503.2]

/-- Complete interval computation for depth 15, residue 28504. -/
theorem bounds_15_28504 : exactInterval 15 28504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28504 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28504) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28504 : oddCount 28504 15 = 9 ∧ acceleratedOrbit 15 28504 = 17131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28504 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28504) = 3 ^ 9 * m + 17131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28504.1, data_15_28504.2]

/-- Complete interval computation for depth 15, residue 28505. -/
theorem bounds_15_28505 : exactInterval 15 28505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28505 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28505) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28505 : oddCount 28505 15 = 8 ∧ acceleratedOrbit 15 28505 = 5710 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28505 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28505) = 3 ^ 8 * m + 5710 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28505.1, data_15_28505.2]

/-- Complete interval computation for depth 15, residue 28506. -/
theorem bounds_15_28506 : exactInterval 15 28506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28506 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28506) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28506 : oddCount 28506 15 = 9 ∧ acceleratedOrbit 15 28506 = 17131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28506 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28506) = 3 ^ 9 * m + 17131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28506.1, data_15_28506.2]

/-- Complete interval computation for depth 15, residue 28507. -/
theorem bounds_15_28507 : exactInterval 15 28507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28507 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28507) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28507 : oddCount 28507 15 = 10 ∧ acceleratedOrbit 15 28507 = 51374 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28507 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28507) = 3 ^ 10 * m + 51374 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28507.1, data_15_28507.2]

end Collatz.Research.PassageAtlas.Batch0870
