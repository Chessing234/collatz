import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0824

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5473. -/
theorem bounds_13_5473 : exactInterval 13 5473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5473 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5473) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5473 : oddCount 5473 13 = 7 ∧ acceleratedOrbit 13 5473 = 1462 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5473 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5473) = 3 ^ 7 * m + 1462 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5473.1, data_13_5473.2]

/-- Complete interval computation for depth 13, residue 5474. -/
theorem bounds_13_5474 : exactInterval 13 5474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5474 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5474) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5474 : oddCount 5474 13 = 5 ∧ acceleratedOrbit 13 5474 = 163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5474 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5474) = 3 ^ 5 * m + 163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5474.1, data_13_5474.2]

/-- Complete interval computation for depth 13, residue 5475. -/
theorem bounds_13_5475 : exactInterval 13 5475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5475 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5475) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5475 : oddCount 5475 13 = 5 ∧ acceleratedOrbit 13 5475 = 163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5475 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5475) = 3 ^ 5 * m + 163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5475.1, data_13_5475.2]

/-- Complete interval computation for depth 13, residue 5476. -/
theorem bounds_13_5476 : exactInterval 13 5476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5476 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5476) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5476 : oddCount 5476 13 = 5 ∧ acceleratedOrbit 13 5476 = 163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5476 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5476) = 3 ^ 5 * m + 163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5476.1, data_13_5476.2]

/-- Complete interval computation for depth 13, residue 5477. -/
theorem bounds_13_5477 : exactInterval 13 5477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5477 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5477) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5477 : oddCount 5477 13 = 5 ∧ acceleratedOrbit 13 5477 = 163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5477 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5477) = 3 ^ 5 * m + 163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5477.1, data_13_5477.2]

/-- Complete interval computation for depth 13, residue 5478. -/
theorem bounds_13_5478 : exactInterval 13 5478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5478 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5478) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5478 : oddCount 5478 13 = 5 ∧ acceleratedOrbit 13 5478 = 163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5478 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5478) = 3 ^ 5 * m + 163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5478.1, data_13_5478.2]

/-- Complete interval computation for depth 13, residue 5479. -/
theorem bounds_13_5479 : exactInterval 13 5479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5479 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5479) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5479 : oddCount 5479 13 = 10 ∧ acceleratedOrbit 13 5479 = 39503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5479 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5479) = 3 ^ 10 * m + 39503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5479.1, data_13_5479.2]

/-- Complete interval computation for depth 13, residue 5480. -/
theorem bounds_13_5480 : exactInterval 13 5480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5480 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5480) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5480 : oddCount 5480 13 = 5 ∧ acceleratedOrbit 13 5480 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5480 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5480) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5480.1, data_13_5480.2]

/-- Complete interval computation for depth 13, residue 5481. -/
theorem bounds_13_5481 : exactInterval 13 5481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5481 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5481) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5481 : oddCount 5481 13 = 6 ∧ acceleratedOrbit 13 5481 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5481 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5481) = 3 ^ 6 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5481.1, data_13_5481.2]

/-- Complete interval computation for depth 13, residue 5482. -/
theorem bounds_13_5482 : exactInterval 13 5482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5482 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5482) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5482 : oddCount 5482 13 = 5 ∧ acceleratedOrbit 13 5482 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5482 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5482) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5482.1, data_13_5482.2]

/-- Complete interval computation for depth 13, residue 5483. -/
theorem bounds_13_5483 : exactInterval 13 5483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5483 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5483) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5483 : oddCount 5483 13 = 8 ∧ acceleratedOrbit 13 5483 = 4394 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5483 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5483) = 3 ^ 8 * m + 4394 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5483.1, data_13_5483.2]

/-- Complete interval computation for depth 13, residue 5484. -/
theorem bounds_13_5484 : exactInterval 13 5484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5484 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5484) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5484 : oddCount 5484 13 = 7 ∧ acceleratedOrbit 13 5484 = 1466 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5484 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5484) = 3 ^ 7 * m + 1466 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5484.1, data_13_5484.2]

/-- Complete interval computation for depth 13, residue 5485. -/
theorem bounds_13_5485 : exactInterval 13 5485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5485 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5485) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5485 : oddCount 5485 13 = 7 ∧ acceleratedOrbit 13 5485 = 1466 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5485 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5485) = 3 ^ 7 * m + 1466 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5485.1, data_13_5485.2]

/-- Complete interval computation for depth 13, residue 5486. -/
theorem bounds_13_5486 : exactInterval 13 5486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5486 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5486) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5486 : oddCount 5486 13 = 7 ∧ acceleratedOrbit 13 5486 = 1466 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5486 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5486) = 3 ^ 7 * m + 1466 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5486.1, data_13_5486.2]

/-- Complete interval computation for depth 13, residue 5487. -/
theorem bounds_13_5487 : exactInterval 13 5487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5487 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5487) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5487 : oddCount 5487 13 = 8 ∧ acceleratedOrbit 13 5487 = 4396 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5487 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5487) = 3 ^ 8 * m + 4396 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5487.1, data_13_5487.2]

end Collatz.Research.StoppingAtlas.Batch0824
