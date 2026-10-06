import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0168

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 5472. -/
theorem bounds_15_5472 : exactInterval 15 5472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5472 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5472) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5472 : oddCount 5472 15 = 5 ∧ acceleratedOrbit 15 5472 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5472 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5472) = 3 ^ 5 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5472.1, data_15_5472.2]

/-- Complete interval computation for depth 15, residue 5473. -/
theorem bounds_15_5473 : exactInterval 15 5473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5473 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5473) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5473 : oddCount 5473 15 = 8 ∧ acceleratedOrbit 15 5473 = 1097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5473 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5473) = 3 ^ 8 * m + 1097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5473.1, data_15_5473.2]

/-- Complete interval computation for depth 15, residue 5474. -/
theorem bounds_15_5474 : exactInterval 15 5474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5474 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5474) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5474 : oddCount 5474 15 = 7 ∧ acceleratedOrbit 15 5474 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5474 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5474) = 3 ^ 7 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5474.1, data_15_5474.2]

/-- Complete interval computation for depth 15, residue 5475. -/
theorem bounds_15_5475 : exactInterval 15 5475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5475 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5475) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5475 : oddCount 5475 15 = 7 ∧ acceleratedOrbit 15 5475 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5475 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5475) = 3 ^ 7 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5475.1, data_15_5475.2]

/-- Complete interval computation for depth 15, residue 5476. -/
theorem bounds_15_5476 : exactInterval 15 5476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5476 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5476) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5476 : oddCount 5476 15 = 7 ∧ acceleratedOrbit 15 5476 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5476 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5476) = 3 ^ 7 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5476.1, data_15_5476.2]

/-- Complete interval computation for depth 15, residue 5477. -/
theorem bounds_15_5477 : exactInterval 15 5477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5477 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5477) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5477 : oddCount 5477 15 = 7 ∧ acceleratedOrbit 15 5477 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5477 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5477) = 3 ^ 7 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5477.1, data_15_5477.2]

/-- Complete interval computation for depth 15, residue 5478. -/
theorem bounds_15_5478 : exactInterval 15 5478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5478 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5478) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5478 : oddCount 5478 15 = 7 ∧ acceleratedOrbit 15 5478 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5478 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5478) = 3 ^ 7 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5478.1, data_15_5478.2]

/-- Complete interval computation for depth 15, residue 5479. -/
theorem bounds_15_5479 : exactInterval 15 5479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5479 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5479) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5479 : oddCount 5479 15 = 12 ∧ acceleratedOrbit 15 5479 = 88883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5479 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5479) = 3 ^ 12 * m + 88883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5479.1, data_15_5479.2]

/-- Complete interval computation for depth 15, residue 5480. -/
theorem bounds_15_5480 : exactInterval 15 5480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5480 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5480) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5480 : oddCount 5480 15 = 5 ∧ acceleratedOrbit 15 5480 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5480 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5480) = 3 ^ 5 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5480.1, data_15_5480.2]

/-- Complete interval computation for depth 15, residue 5481. -/
theorem bounds_15_5481 : exactInterval 15 5481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5481 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5481) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5481 : oddCount 5481 15 = 6 ∧ acceleratedOrbit 15 5481 = 122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5481 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5481) = 3 ^ 6 * m + 122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5481.1, data_15_5481.2]

/-- Complete interval computation for depth 15, residue 5482. -/
theorem bounds_15_5482 : exactInterval 15 5482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5482 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5482) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5482 : oddCount 5482 15 = 5 ∧ acceleratedOrbit 15 5482 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5482 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5482) = 3 ^ 5 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5482.1, data_15_5482.2]

/-- Complete interval computation for depth 15, residue 5483. -/
theorem bounds_15_5483 : exactInterval 15 5483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5483 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5483) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5483 : oddCount 5483 15 = 9 ∧ acceleratedOrbit 15 5483 = 3296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5483 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5483) = 3 ^ 9 * m + 3296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5483.1, data_15_5483.2]

/-- Complete interval computation for depth 15, residue 5484. -/
theorem bounds_15_5484 : exactInterval 15 5484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5484 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5484) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5484 : oddCount 5484 15 = 8 ∧ acceleratedOrbit 15 5484 = 1100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5484 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5484) = 3 ^ 8 * m + 1100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5484.1, data_15_5484.2]

/-- Complete interval computation for depth 15, residue 5485. -/
theorem bounds_15_5485 : exactInterval 15 5485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5485 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5485) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5485 : oddCount 5485 15 = 8 ∧ acceleratedOrbit 15 5485 = 1100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5485 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5485) = 3 ^ 8 * m + 1100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5485.1, data_15_5485.2]

/-- Complete interval computation for depth 15, residue 5486. -/
theorem bounds_15_5486 : exactInterval 15 5486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5486 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5486) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5486 : oddCount 5486 15 = 8 ∧ acceleratedOrbit 15 5486 = 1100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5486 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5486) = 3 ^ 8 * m + 1100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5486.1, data_15_5486.2]

/-- Complete interval computation for depth 15, residue 5487. -/
theorem bounds_15_5487 : exactInterval 15 5487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5487 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5487) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5487 : oddCount 5487 15 = 8 ∧ acceleratedOrbit 15 5487 = 1099 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5487 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5487) = 3 ^ 8 * m + 1099 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5487.1, data_15_5487.2]

/-- Complete interval computation for depth 15, residue 5488. -/
theorem bounds_15_5488 : exactInterval 15 5488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5488 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5488) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5488 : oddCount 5488 15 = 5 ∧ acceleratedOrbit 15 5488 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5488 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5488) = 3 ^ 5 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5488.1, data_15_5488.2]

/-- Complete interval computation for depth 15, residue 5489. -/
theorem bounds_15_5489 : exactInterval 15 5489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5489 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5489) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5489 : oddCount 5489 15 = 5 ∧ acceleratedOrbit 15 5489 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5489 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5489) = 3 ^ 5 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5489.1, data_15_5489.2]

/-- Complete interval computation for depth 15, residue 5490. -/
theorem bounds_15_5490 : exactInterval 15 5490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5490 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5490) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5490 : oddCount 5490 15 = 7 ∧ acceleratedOrbit 15 5490 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5490 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5490) = 3 ^ 7 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5490.1, data_15_5490.2]

/-- Complete interval computation for depth 15, residue 5491. -/
theorem bounds_15_5491 : exactInterval 15 5491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5491 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5491) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5491 : oddCount 5491 15 = 7 ∧ acceleratedOrbit 15 5491 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5491 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5491) = 3 ^ 7 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5491.1, data_15_5491.2]

/-- Complete interval computation for depth 15, residue 5492. -/
theorem bounds_15_5492 : exactInterval 15 5492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5492 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5492) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5492 : oddCount 5492 15 = 5 ∧ acceleratedOrbit 15 5492 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5492 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5492) = 3 ^ 5 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5492.1, data_15_5492.2]

/-- Complete interval computation for depth 15, residue 5493. -/
theorem bounds_15_5493 : exactInterval 15 5493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5493 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5493) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5493 : oddCount 5493 15 = 5 ∧ acceleratedOrbit 15 5493 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5493 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5493) = 3 ^ 5 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5493.1, data_15_5493.2]

/-- Complete interval computation for depth 15, residue 5494. -/
theorem bounds_15_5494 : exactInterval 15 5494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5494 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5494) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5494 : oddCount 5494 15 = 7 ∧ acceleratedOrbit 15 5494 = 367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5494 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5494) = 3 ^ 7 * m + 367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5494.1, data_15_5494.2]

/-- Complete interval computation for depth 15, residue 5495. -/
theorem bounds_15_5495 : exactInterval 15 5495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5495 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5495) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5495 : oddCount 5495 15 = 7 ∧ acceleratedOrbit 15 5495 = 367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5495 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5495) = 3 ^ 7 * m + 367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5495.1, data_15_5495.2]

/-- Complete interval computation for depth 15, residue 5496. -/
theorem bounds_15_5496 : exactInterval 15 5496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5496 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5496) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5496 : oddCount 5496 15 = 7 ∧ acceleratedOrbit 15 5496 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5496 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5496) = 3 ^ 7 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5496.1, data_15_5496.2]

/-- Complete interval computation for depth 15, residue 5497. -/
theorem bounds_15_5497 : exactInterval 15 5497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5497 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5497) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5497 : oddCount 5497 15 = 10 ∧ acceleratedOrbit 15 5497 = 9910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5497 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5497) = 3 ^ 10 * m + 9910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5497.1, data_15_5497.2]

/-- Complete interval computation for depth 15, residue 5498. -/
theorem bounds_15_5498 : exactInterval 15 5498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5498 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5498) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5498 : oddCount 5498 15 = 7 ∧ acceleratedOrbit 15 5498 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5498 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5498) = 3 ^ 7 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5498.1, data_15_5498.2]

/-- Complete interval computation for depth 15, residue 5499. -/
theorem bounds_15_5499 : exactInterval 15 5499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5499 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5499) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5499 : oddCount 5499 15 = 8 ∧ acceleratedOrbit 15 5499 = 1102 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5499 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5499) = 3 ^ 8 * m + 1102 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5499.1, data_15_5499.2]

/-- Complete interval computation for depth 15, residue 5500. -/
theorem bounds_15_5500 : exactInterval 15 5500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5500 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5500) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5500 : oddCount 5500 15 = 7 ∧ acceleratedOrbit 15 5500 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5500 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5500) = 3 ^ 7 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5500.1, data_15_5500.2]

/-- Complete interval computation for depth 15, residue 5501. -/
theorem bounds_15_5501 : exactInterval 15 5501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5501 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5501) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5501 : oddCount 5501 15 = 7 ∧ acceleratedOrbit 15 5501 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5501 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5501) = 3 ^ 7 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5501.1, data_15_5501.2]

/-- Complete interval computation for depth 15, residue 5502. -/
theorem bounds_15_5502 : exactInterval 15 5502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5502 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5502) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5502 : oddCount 5502 15 = 10 ∧ acceleratedOrbit 15 5502 = 9919 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5502 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5502) = 3 ^ 10 * m + 9919 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5502.1, data_15_5502.2]

/-- Complete interval computation for depth 15, residue 5503. -/
theorem bounds_15_5503 : exactInterval 15 5503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5503 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5503) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5503 : oddCount 5503 15 = 10 ∧ acceleratedOrbit 15 5503 = 9919 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5503 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5503) = 3 ^ 10 * m + 9919 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5503.1, data_15_5503.2]

/-- Complete interval computation for depth 15, residue 5504. -/
theorem bounds_15_5504 : exactInterval 15 5504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5504 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5504) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5504 : oddCount 5504 15 = 4 ∧ acceleratedOrbit 15 5504 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5504 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5504) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5504.1, data_15_5504.2]

end Collatz.Research.PassageAtlas.Batch0168
