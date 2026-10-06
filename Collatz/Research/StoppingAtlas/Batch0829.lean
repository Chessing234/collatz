import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0829

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5550. -/
theorem bounds_13_5550 : exactInterval 13 5550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5550 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5550) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5550 : oddCount 5550 13 = 7 ∧ acceleratedOrbit 13 5550 = 1484 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5550 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5550) = 3 ^ 7 * m + 1484 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5550.1, data_13_5550.2]

/-- Complete interval computation for depth 13, residue 5551. -/
theorem bounds_13_5551 : exactInterval 13 5551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5551 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5551) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5551 : oddCount 5551 13 = 8 ∧ acceleratedOrbit 13 5551 = 4448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5551 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5551) = 3 ^ 8 * m + 4448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5551.1, data_13_5551.2]

/-- Complete interval computation for depth 13, residue 5552. -/
theorem bounds_13_5552 : exactInterval 13 5552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5552 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5552) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5552 : oddCount 5552 13 = 6 ∧ acceleratedOrbit 13 5552 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5552 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5552) = 3 ^ 6 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5552.1, data_13_5552.2]

/-- Complete interval computation for depth 13, residue 5553. -/
theorem bounds_13_5553 : exactInterval 13 5553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5553 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5553) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5553 : oddCount 5553 13 = 4 ∧ acceleratedOrbit 13 5553 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5553 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5553) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5553.1, data_13_5553.2]

/-- Complete interval computation for depth 13, residue 5554. -/
theorem bounds_13_5554 : exactInterval 13 5554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5554 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5554) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5554 : oddCount 5554 13 = 4 ∧ acceleratedOrbit 13 5554 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5554 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5554) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5554.1, data_13_5554.2]

/-- Complete interval computation for depth 13, residue 5555. -/
theorem bounds_13_5555 : exactInterval 13 5555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5555 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5555) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5555 : oddCount 5555 13 = 4 ∧ acceleratedOrbit 13 5555 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5555 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5555) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5555.1, data_13_5555.2]

/-- Complete interval computation for depth 13, residue 5556. -/
theorem bounds_13_5556 : exactInterval 13 5556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5556 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5556) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5556 : oddCount 5556 13 = 6 ∧ acceleratedOrbit 13 5556 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5556 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5556) = 3 ^ 6 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5556.1, data_13_5556.2]

/-- Complete interval computation for depth 13, residue 5557. -/
theorem bounds_13_5557 : exactInterval 13 5557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5557 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5557) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5557 : oddCount 5557 13 = 6 ∧ acceleratedOrbit 13 5557 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5557 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5557) = 3 ^ 6 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5557.1, data_13_5557.2]

/-- Complete interval computation for depth 13, residue 5558. -/
theorem bounds_13_5558 : exactInterval 13 5558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5558 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5558) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5558 : oddCount 5558 13 = 9 ∧ acceleratedOrbit 13 5558 = 13364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5558 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5558) = 3 ^ 9 * m + 13364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5558.1, data_13_5558.2]

/-- Complete interval computation for depth 13, residue 5559. -/
theorem bounds_13_5559 : exactInterval 13 5559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5559 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5559) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5559 : oddCount 5559 13 = 9 ∧ acceleratedOrbit 13 5559 = 13364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5559 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5559) = 3 ^ 9 * m + 13364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5559.1, data_13_5559.2]

/-- Complete interval computation for depth 13, residue 5560. -/
theorem bounds_13_5560 : exactInterval 13 5560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5560 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5560) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5560 : oddCount 5560 13 = 6 ∧ acceleratedOrbit 13 5560 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5560 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5560) = 3 ^ 6 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5560.1, data_13_5560.2]

/-- Complete interval computation for depth 13, residue 5561. -/
theorem bounds_13_5561 : exactInterval 13 5561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5561 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5561) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5561 : oddCount 5561 13 = 4 ∧ acceleratedOrbit 13 5561 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5561 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5561) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5561.1, data_13_5561.2]

/-- Complete interval computation for depth 13, residue 5562. -/
theorem bounds_13_5562 : exactInterval 13 5562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5562 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5562) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5562 : oddCount 5562 13 = 6 ∧ acceleratedOrbit 13 5562 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5562 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5562) = 3 ^ 6 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5562.1, data_13_5562.2]

/-- Complete interval computation for depth 13, residue 5563. -/
theorem bounds_13_5563 : exactInterval 13 5563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5563 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5563) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5563 : oddCount 5563 13 = 7 ∧ acceleratedOrbit 13 5563 = 1486 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5563 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5563) = 3 ^ 7 * m + 1486 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5563.1, data_13_5563.2]

/-- Complete interval computation for depth 13, residue 5564. -/
theorem bounds_13_5564 : exactInterval 13 5564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5564 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5564) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5564 : oddCount 5564 13 = 7 ∧ acceleratedOrbit 13 5564 = 1487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5564 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5564) = 3 ^ 7 * m + 1487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5564.1, data_13_5564.2]

end Collatz.Research.StoppingAtlas.Batch0829
